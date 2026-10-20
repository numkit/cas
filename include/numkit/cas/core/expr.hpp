// core/expr.hpp — hash-consed immutable expression DAG.
#pragma once

#include <numkit/cas/num/rational.hpp>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace numkit::cas {

enum class NodeKind : std::uint8_t {
    Number, // Rational atom
    Symbol, // named variable / named constant later
    Pow,    // Pow(base, exp); canonical rules fold numeric cases
    Func,   // Func(name, arg): sin, cos, tan, atan, exp, log, ...
    Add,    // n-ary, AC, children canonical + sorted
    Mul,    // n-ary, AC, children canonical + sorted
    RootOf, // algebraic number atom: root #index of a monic polynomial
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

    // Algebraic number atom: the root #index (0-based, in ascending
    // real order) of a MONIC polynomial of degree >= 2 with rational
    // coefficients (ascending). The polynomial is stored canonically
    // (trimmed, monic); identical (poly, index) pairs intern to the
    // same node. Callers extract rational roots themselves.
    Expr rootOf(std::vector<Rational> poly, int index);
    const std::vector<Rational> &rootOfPoly(Expr e) const;
    int rootOfIndex(Expr e) const;

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

    // True iff e is the canonical zero Number node.
    bool isZero(Expr e) const
    {
        return kind(e) == NodeKind::Number && numberValue(e).isZero();
    }

    // Symbolic derivative d/de of e. var must be a Symbol node.
    // Supported functions: exp, log, sin, cos, tan, atan, asin, acos,
    // sinh, cosh, tanh, asinh, acosh, atanh; anything else
    // asserts in debug and returns a null Expr in release.
    Expr diff(Expr e, Expr var);

    // Substitute: rebuild e with every occurrence of the subtree
    // `from` replaced by `to` (comparison is node identity, i.e.
    // structural equality via hash-consing). The rebuilt nodes go
    // through the canonicalizing constructors, so e.g. substituting
    // x -> 2 in x^2 yields the number 4.
    Expr subs(Expr e, Expr from, Expr to);

    // Distribute products and integer powers over sums: a fully
    // expanded canonical polynomial-form expression (like terms
    // collected by the Add/Mul canonicalization). Fractional powers
    // stay as powers; negative integer powers distribute
    // multiplicatively over the expanded base. Blow-up is the
    // caller's responsibility (as in MATLAB's expand).
    Expr expand(Expr e);

    // Exact rational evaluation of e with the given symbol values.
    // Returns false when any intermediate leaves Q: unresolved
    // symbols, RootOf atoms, fractional powers, transcendental
    // functions at non-trivial points (the trivial identities
    // exp(0)=1, log(1)=0, sin/tan/atan(0)=0, cos(0)=1 do evaluate).
    // This is the vpa groundwork: exact when possible, honest
    // decline otherwise.
    bool evalExact(
        Expr e,
        const std::vector<std::pair<std::string, Rational>> &vals,
        Rational &out);

    std::string toString(Expr e) const;

    // Tree-based leaf/head count (Mathematica/Rubi LeafCount convention):
    // 1 for atoms (Number, Symbol, RootOf), 1 + sum(child leafCounts) for
    // compound nodes (Pow, Func, Add, Mul), 0 for a null Expr.
    std::size_t leafCount(Expr e) const;

    // Section 6 discrete DAG cost functional C(F) = sum_{v in DAG(F)} NodeCost(v)
    // over unique reachable DAG nodes (1 for Number/Symbol/RootOf/Add/Mul/Pow,
    // 3 for elementary transcendental Func, 5 for abs inside log, 10 for
    // special functions).
    std::size_t exprCost(Expr e) const;

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
    Expr diffRec(Expr e, Expr var, std::unordered_map<std::uint32_t, Expr> &memo);

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
    // RootOf payload table (index by node aux). Coefficients ascending;
    // stored as plain vectors to keep the core layer independent of
    // the poly layer.
    struct RootOfDesc
    {
        std::vector<Rational> poly;
        int index;
        std::uint32_t nodeId = 0; // id of the interning node (filled after makeNode)
    };
    std::deque<RootOfDesc> rootofs_;
};

} // namespace numkit::cas
