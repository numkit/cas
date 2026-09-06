// core/expr.hpp — hash-consed immutable expression DAG.
#pragma once

#include <numkit/cas/num/rational.hpp>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <string>
#include <unordered_map>
#include <vector>

namespace numkit::cas {

enum class NodeKind : std::uint8_t {
    Number, // Rational atom
    Symbol, // named variable / named constant later
    Pow,    // Pow(base, exp); canonical rules fold numeric cases
    Func,   // Func(name, arg): sin, cos, tan, atan, exp, log, ...
    Add,    // n-ary, AC, children canonical + sorted
    Mul,    // n-ary, AC, children canonical + sorted
};

// ============================================================
// Expr — a thin handle into a Ctx-owned interned arena.
//
// Nodes are immutable and hash-consed: structurally equal expressions
// within one Ctx are the SAME node, so Expr equality is id comparison.
// An Expr is only meaningful inside its owning Ctx (asserted in debug).
// Default-constructed Expr is null (isNull()).
// ============================================================
class Ctx;

class Expr
{
public:
    Expr() = default;

    bool isNull() const { return ctx_ == nullptr; }
    Ctx &ctx() const
    {
        assert(ctx_ != nullptr);
        return *ctx_;
    }

    friend bool operator==(const Expr &a, const Expr &b)
    {
        assert(a.ctx_ == b.ctx_ && "Expr from different Ctx");
        return a.id_ == b.id_;
    }
    friend bool operator!=(const Expr &a, const Expr &b) { return !(a == b); }

private:
    friend class Ctx;
    Expr(Ctx *ctx, std::uint32_t id) : ctx_(ctx), id_(id) {}

    Ctx *ctx_ = nullptr;
    std::uint32_t id_ = 0;
};

struct Node
{
    NodeKind kind = NodeKind::Number;
    std::uint32_t aux = 0;      // symbol id or func id (name tables in Ctx)
    std::uint32_t childOff = 0; // offset into Ctx child arena
    std::uint32_t childCount = 0;
    std::uint32_t hash = 0;
    Rational num; // Number kind only
};

// ============================================================
// Ctx — owner of the interned node arena, symbol/func name tables
// and the hash-consing table. No global state; one Ctx per problem
// (later: per worker). All constructors canonicalize:
//   - Add/Mul: flattened, numeric constants folded, equal children
//     merged into integer coefficients / powers, children sorted by
//     the total order of compare();
//   - Pow: x^0 -> 1, x^1 -> x, numeric folding for integer exponents,
//     (u^a)^n -> u^(a*n) for integer n, (Mul)^n distributed for
//     integer n.
// ============================================================
class Ctx
{
public:
    // ── construction ──────────────────────────────────────────
    Expr number(std::int64_t v);
    Expr number(Rational v);
    Expr zero() { return number(std::int64_t{0}); }
    Expr one() { return number(std::int64_t{1}); }

    Expr symbol(const std::string &name);

    Expr add(const std::vector<Expr> &children) { return makeAdd(children); }
    Expr mul(const std::vector<Expr> &children) { return makeMul(children); }
    Expr pow(Expr base, Expr exp);
    Expr func(const std::string &name, Expr arg);

    Expr neg(Expr a);             // (-1) * a
    Expr div(Expr a, Expr b);     // a * b^(-1); b must be non-zero Number

    // ── observation ───────────────────────────────────────────
    NodeKind kind(Expr e) const { return node(e).kind; }
    const Rational &numberValue(Expr e) const { return node(e).num; }
    const std::string &symbolName(Expr e) const;
    const std::string &funcName(Expr e) const;
    std::size_t childCount(Expr e) const { return node(e).childCount; }
    Expr child(Expr e, std::size_t i) const;

    // Total structural order, consistent with == (identical => 0).
    // Kind rank: Number < Symbol < Pow < Func < Add < Mul; then
    // value/name, then children lexicographically.
    int compare(Expr a, Expr b) const;

    std::string toString(Expr e) const;

    std::size_t nodeCount() const { return nodes_.size(); }

    // Stable per-Ctx node identity (1-based; matches insertion order).
    std::uint32_t id(Expr e) const
    {
        assert(e.ctx_ == this && !e.isNull());
        return e.id_;
    }

private:
    friend class Expr;

    const Node &node(Expr e) const
    {
        assert(e.ctx_ == this && !e.isNull());
        return nodes_[e.id_ - 1];
    }

    std::uint32_t internName(const std::string &name,
                             std::unordered_map<std::string, std::uint32_t> &ids,
                             std::deque<std::string> &names);

    Expr makeNode(NodeKind kind, std::uint32_t aux,
                  const std::vector<Expr> &children, const Rational &num);
    bool equalNode(const Node &n, NodeKind kind, std::uint32_t aux,
                   const std::vector<Expr> &children, const Rational &num) const;

    Expr makeAdd(const std::vector<Expr> &children);
    Expr makeMul(const std::vector<Expr> &children);
    bool smallInteger(const Rational &e, std::int64_t &n) const;

    void print(Expr e, std::string &out) const;
    void printPrec(Expr e, std::string &out, int parentPrec) const;
    static int kindRank(NodeKind k);

    std::deque<Node> nodes_;
    std::vector<std::uint32_t> childArena_;
    std::unordered_multimap<std::uint32_t, std::uint32_t> intern_;
    std::unordered_map<std::string, std::uint32_t> symbolIds_;
    std::unordered_map<std::string, std::uint32_t> funcIds_;
    std::deque<std::string> symbolNames_;
    std::deque<std::string> funcNames_;
};

} // namespace numkit::cas
