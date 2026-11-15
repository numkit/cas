// core/expr.hpp — hash-consed immutable expression DAG.
#pragma once

#include <keel/core.h>
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

enum class NodeKind : keel::u8 {
    Number, // Rational atom
    Symbol, // named variable / named constant later
    Pow,    // Pow(base, exp); canonical rules fold numeric cases
    Func,   // Func(name, arg): sin, cos, tan, atan, exp, log, ...
    Add,    // n-ary, AC, children canonical + sorted
    Mul,    // n-ary, AC, children canonical + sorted
    RootOf, // algebraic number atom: root #index of a monic polynomial
};

enum class AssumeDomain : keel::u8 {
    Any = 0,     // unconstrained symbol (default)
    Real,        // x in R
    Positive,    // x in R, x > 0
    Negative,    // x in R, x < 0
    NonNegative, // x in R, x >= 0
    Integer,     // x in Z
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
    Expr(Ctx *ctx, keel::u32 id) : ctx_(ctx), id_(id) {}

    Ctx *ctx_ = nullptr;
    keel::u32 id_ = 0;
};

struct Node
{
    NodeKind kind = NodeKind::Number;
    keel::u32 aux = 0;      // symbol id or func id (name tables in Ctx)
    keel::u32 childOff = 0; // offset into Ctx child arena
    keel::u32 childCount = 0;
    keel::u32 hash = 0;
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
    Expr number(keel::i64 v);
    Expr number(Rational v);
    Expr zero() { return number(keel::i64{0}); }
    Expr one() { return number(keel::i64{1}); }

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
    Expr func(const std::string &name, Expr arg0, Expr arg1);
    Expr func(const std::string &name, const std::vector<Expr> &args);

    Expr neg(Expr a);             // (-1) * a
    Expr div(Expr a, Expr b);     // a * b^(-1); b must be non-zero Number

    // ── observation ───────────────────────────────────────────
    NodeKind kind(Expr e) const { return node(e).kind; }
    const Rational &numberValue(Expr e) const { return node(e).num; }
    const std::string &symbolName(Expr e) const;
    const std::string &funcName(Expr e) const;
    keel::usize childCount(Expr e) const { return node(e).childCount; }
    Expr child(Expr e, keel::usize i) const;

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

    // Cost-guided algebraic, rational, and trigonometric simplification
    // minimizing (exprCost, leafCount).
    Expr simplify(Expr e);

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

    // Real IEEE-754 double evaluation (vpa/double bridge, item 35):
    // evaluates Number (via Rational::toDouble), Symbol (from `vals`, with
    // built-in fallback for "pi" and "e"), RootOf (via Sturm isolation +
    // 56-bit interval refinement), Pow (including odd roots of negatives),
    // and elementary/special functions (exp, log, sqrt, abs, trig, inverse
    // trig, hyperbolic, inverse hyperbolic, erf, erfc, gamma). Memoized over
    // the expression DAG. Returns false on unresolved symbols, complex
    // values, poles, or non-finite overflow.
    bool evalDouble(
        Expr e,
        const std::vector<std::pair<std::string, keel::f64>> &vals,
        keel::f64 &out) const;

    std::string toString(Expr e) const;

    // Tree-based leaf/head count (Mathematica/Rubi LeafCount convention):
    // 1 for atoms (Number, Symbol, RootOf), 1 + sum(child leafCounts) for
    // compound nodes (Pow, Func, Add, Mul), 0 for a null Expr.
    keel::usize leafCount(Expr e) const;

    // Section 6 discrete DAG cost functional C(F) = sum_{v in DAG(F)} NodeCost(v)
    // over unique reachable DAG nodes (1 for Number/Symbol/RootOf/Add/Mul/Pow,
    // 3 for elementary transcendental Func, 5 for abs inside log, 10 for
    // special functions).
    keel::usize exprCost(Expr e) const;

    keel::usize nodeCount() const { return nodes_.size(); }

    // Stable per-Ctx node identity (1-based; matches insertion order).
    keel::u32 id(Expr e) const
    {
        assert(e.ctx_ == this && !e.isNull());
        return e.id_;
    }

    // ── symbol assumptions (item 45) ──────────────────────────
    void assume(const std::string &name, AssumeDomain dom);
    void assume(Expr sym, AssumeDomain dom);
    AssumeDomain assumption(const std::string &name) const;
    AssumeDomain assumption(Expr sym) const;
    void clearAssumptions();

    bool isAssumedPositive(Expr e) const;
    bool isAssumedNegative(Expr e) const;
    bool isAssumedNonNegative(Expr e) const;
    bool isAssumedReal(Expr e) const;
    bool isAssumedInteger(Expr e) const;

private:
    friend class Expr;

    const Node &node(Expr e) const
    {
        assert(e.ctx_ == this && !e.isNull());
        return nodes_[e.id_ - 1];
    }

    keel::u32 internName(const std::string &name,
                             std::unordered_map<std::string, keel::u32> &ids,
                             std::deque<std::string> &names);

    Expr makeNode(NodeKind kind, keel::u32 aux,
                  const std::vector<Expr> &children, const Rational &num);
    bool equalNode(const Node &n, NodeKind kind, keel::u32 aux,
                   const std::vector<Expr> &children, const Rational &num) const;

    Expr makeAdd(const std::vector<Expr> &children);
    Expr makeMul(const std::vector<Expr> &children);
    bool smallInteger(const Rational &e, keel::i64 &n) const;
    Expr diffRec(Expr e, Expr var, std::unordered_map<keel::u32, Expr> &memo);

    void print(Expr e, std::string &out) const;
    void printPrec(Expr e, std::string &out, int parentPrec) const;
    static int kindRank(NodeKind k);

    std::deque<Node> nodes_;
    std::vector<keel::u32> childArena_;
    std::unordered_multimap<keel::u32, keel::u32> intern_;
    std::unordered_map<std::string, keel::u32> symbolIds_;
    std::unordered_map<std::string, keel::u32> funcIds_;
    std::deque<std::string> symbolNames_;
    std::deque<std::string> funcNames_;
    // RootOf payload table (index by node aux). Coefficients ascending;
    // stored as plain vectors to keep the core layer independent of
    // the poly layer.
    struct RootOfDesc
    {
        std::vector<Rational> poly;
        int index;
        keel::u32 nodeId = 0; // id of the interning node (filled after makeNode)
    };
    std::deque<RootOfDesc> rootofs_;
    std::unordered_map<std::string, AssumeDomain> assumptions_;
};

} // namespace numkit::cas
