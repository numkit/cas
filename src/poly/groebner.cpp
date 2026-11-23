// src/poly/groebner.cpp — Buchberger's algorithm for reduced Groebner bases over Q[x_1, ..., x_k].
#include <keel/core.h>
#include <numkit/cas/poly/groebner.hpp>

#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/cas/poly/upoly.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

#include <algorithm>
#include <numeric>
#include <keel/algo.h>
#include <keel/string.h>
#include <utility>
#include <keel/array.h>

namespace numkit::cas {
namespace {

bool checkGroebnerBudget(const Ctx &c, Budget *budget, keel::String &reason)
{
    if (!budget)
        return true;
    if (budget->step() && budget->recordArenaBytes(c.nodeCount() * 32))
        return true;
    reason.assign(budget->status() == BudgetStatus::StepExhausted
                 ? "step budget exhausted"
                 : "arena byte budget exhausted");
    return false;
}

struct MTerm
{
    Rational coeff;
    keel::Array<keel::i32> exp; // exponents of vars[0..k-1]

    MTerm() noexcept = default;
    MTerm(Rational c, keel::Array<keel::i32> e) noexcept : coeff(keel::move(c)), exp(keel::move(e)) {}
    MTerm(const MTerm &o) : coeff(o.coeff), exp(o.exp.clone()) {}
    MTerm &operator=(const MTerm &o)
    {
        if (this != &o) {
            coeff = o.coeff;
            exp = o.exp.clone();
        }
        return *this;
    }
    MTerm(MTerm &&) noexcept = default;
    MTerm &operator=(MTerm &&) noexcept = default;
};

keel::i32 totalDegree(const keel::Array<keel::i32> &a)
{
    keel::i32 s = 0;
    for (keel::i32 e : a)
        s += e;
    return s;
}

// Return > 0 if monomial `a` > `b` under `order`, < 0 if `a` < `b`, 0 if `a == b`.
keel::i32 compareMonomial(const keel::Array<keel::i32> &a, const keel::Array<keel::i32> &b,
                    MonomialOrder order)
{
    const keel::usize k = a.size();
    if (order == MonomialOrder::Lex) {
        for (keel::usize i = 0; i < k; ++i) {
            if (a[i] != b[i])
                return (a[i] > b[i]) ? 1 : -1;
        }
        return 0;
    }
    // GrevLex: compare total degree first; break ties by the LAST variable
    // where exponents differ (smaller exponent in the last variable wins).
    const keel::i32 da = totalDegree(a);
    const keel::i32 db = totalDegree(b);
    if (da != db)
        return (da > db) ? 1 : -1;
    for (keel::usize idx = k; idx > 0; --idx) {
        const keel::usize i = idx - 1;
        if (a[i] != b[i])
            return (a[i] < b[i]) ? 1 : -1;
    }
    return 0;
}

bool monomialDivides(const keel::Array<keel::i32> &divisor,
                     const keel::Array<keel::i32> &target)
{
    for (keel::usize i = 0; i < divisor.size(); ++i) {
        if (divisor[i] > target[i])
            return false;
    }
    return true;
}

bool monomialsCoprime(const keel::Array<keel::i32> &a, const keel::Array<keel::i32> &b)
{
    for (keel::usize i = 0; i < a.size(); ++i) {
        if (a[i] > 0 && b[i] > 0)
            return false;
    }
    return true;
}

keel::Array<keel::i32> monomialLcm(const keel::Array<keel::i32> &a,
                             const keel::Array<keel::i32> &b)
{
    keel::Array<keel::i32> out(a.size(), 0);
    for (keel::usize i = 0; i < a.size(); ++i)
        out[i] = std::max(a[i], b[i]);
    return out;
}

keel::Array<keel::i32> monomialSub(const keel::Array<keel::i32> &a,
                             const keel::Array<keel::i32> &b)
{
    keel::Array<keel::i32> out(a.size(), 0);
    for (keel::usize i = 0; i < a.size(); ++i)
        out[i] = a[i] - b[i];
    return out;
}

keel::Array<keel::i32> monomialAdd(const keel::Array<keel::i32> &a,
                             const keel::Array<keel::i32> &b)
{
    keel::Array<keel::i32> out(a.size(), 0);
    for (keel::usize i = 0; i < a.size(); ++i)
        out[i] = a[i] + b[i];
    return out;
}

// Sparse multivariate polynomial with terms sorted in strictly descending
// monomial order (`terms[0]` is the leading term).
struct MPoly
{
    keel::Array<MTerm> terms;

    MPoly() noexcept = default;
    MPoly(const MPoly &o) : terms(o.terms.clone()) {}
    MPoly &operator=(const MPoly &o)
    {
        if (this != &o)
            terms = o.terms.clone();
        return *this;
    }
    MPoly(MPoly &&) noexcept = default;
    MPoly &operator=(MPoly &&) noexcept = default;

    bool isZero() const { return terms.empty(); }
    const MTerm &lt() const { return terms.front(); }
};

void normalizeMPoly(MPoly &p, MonomialOrder order)
{
    if (p.terms.empty())
        return;
    std::sort(p.terms.begin(), p.terms.end(),
              [&](const MTerm &x, const MTerm &y) {
                  return compareMonomial(x.exp, y.exp, order) > 0;
              });
    keel::Array<MTerm> merged;
    merged.reserve(p.terms.size());
    for (const MTerm &t : p.terms) {
        if (t.coeff.isZero())
            continue;
        if (!merged.empty() && merged.back().exp == t.exp) {
            merged.back().coeff = merged.back().coeff + t.coeff;
            if (merged.back().coeff.isZero())
                merged.pop_back();
        } else {
            merged.push_back(t);
        }
    }
    p.terms = std::move(merged);
}

MPoly mpolyAdd(const MPoly &a, const MPoly &b, MonomialOrder order)
{
    MPoly out;
    out.terms.reserve(a.terms.size() + b.terms.size());
    keel::usize i = 0, j = 0;
    while (i < a.terms.size() && j < b.terms.size()) {
        const keel::i32 cmp = compareMonomial(a.terms[i].exp, b.terms[j].exp, order);
        if (cmp > 0) {
            out.terms.push_back(a.terms[i++]);
        } else if (cmp < 0) {
            out.terms.push_back(b.terms[j++]);
        } else {
            const Rational c = a.terms[i].coeff + b.terms[j].coeff;
            if (!c.isZero())
                out.terms.push_back(MTerm{c, a.terms[i].exp.clone()});
            ++i;
            ++j;
        }
    }
    while (i < a.terms.size())
        out.terms.push_back(a.terms[i++]);
    while (j < b.terms.size())
        out.terms.push_back(b.terms[j++]);
    return out;
}

MPoly mpolySub(const MPoly &a, const MPoly &b, MonomialOrder order)
{
    MPoly negB = b;
    for (MTerm &t : negB.terms)
        t.coeff = -t.coeff;
    return mpolyAdd(a, negB, order);
}

MPoly mpolyMulTerm(const MPoly &a, const Rational &c,
                   const keel::Array<keel::i32> &expShift)
{
    MPoly out;
    if (c.isZero() || a.isZero())
        return out;
    out.terms.reserve(a.terms.size());
    for (const MTerm &t : a.terms) {
        out.terms.push_back(MTerm{t.coeff * c, monomialAdd(t.exp, expShift)});
    }
    return out;
}

MPoly mpolyMul(const MPoly &a, const MPoly &b, MonomialOrder order)
{
    if (a.isZero() || b.isZero())
        return MPoly{};
    MPoly out;
    out.terms.reserve(a.terms.size() * b.terms.size());
    for (const MTerm &ta : a.terms) {
        for (const MTerm &tb : b.terms) {
            out.terms.push_back(
                MTerm{ta.coeff * tb.coeff, monomialAdd(ta.exp, tb.exp)});
        }
    }
    normalizeMPoly(out, order);
    return out;
}

void mpolyMakeMonic(MPoly &p)
{
    if (p.isZero())
        return;
    const Rational lead = p.terms.front().coeff;
    if (lead == Rational(keel::i64{1}))
        return;
    for (MTerm &t : p.terms)
        t.coeff = t.coeff / lead;
}

// S-polynomial S(f, g) = (lcm / LT(f)) * f - (lcm / LT(g)) * g
MPoly mpolySPoly(const MPoly &f, const MPoly &g, MonomialOrder order)
{
    const keel::Array<keel::i32> lcm = monomialLcm(f.lt().exp, g.lt().exp);
    const keel::Array<keel::i32> df = monomialSub(lcm, f.lt().exp);
    const keel::Array<keel::i32> dg = monomialSub(lcm, g.lt().exp);
    const Rational cf = Rational(keel::i64{1}) / f.lt().coeff;
    const Rational cg = Rational(keel::i64{1}) / g.lt().coeff;
    return mpolySub(mpolyMulTerm(f, cf, df), mpolyMulTerm(g, cg, dg), order);
}

// Multivariate polynomial division of `f` by `G`: reduces all terms of `f`
// modulo the leading terms of `G`, returning the normal form remainder `r`.
bool mpolyReduce(const Ctx &c, const MPoly &f, const keel::Array<MPoly> &G,
                 MonomialOrder order, Budget *budget, MPoly &rOut,
                 keel::String &reason)
{
    MPoly p = f;
    rOut.terms.clear();
    keel::usize iter = 0;
    constexpr keel::usize kMaxDivSteps = 8192;

    while (!p.isZero()) {
        if (++iter > kMaxDivSteps) {
            reason.assign("multivariate division step limit exceeded");
            return false;
        }
        if ((iter & 15u) == 0u && !checkGroebnerBudget(c, budget, reason))
            return false;

        const MTerm ltP = p.lt();
        bool divided = false;
        for (const MPoly &g : G) {
            if (g.isZero())
                continue;
            if (monomialDivides(g.lt().exp, ltP.exp)) {
                const Rational qCoeff = ltP.coeff / g.lt().coeff;
                const keel::Array<keel::i32> qExp = monomialSub(ltP.exp, g.lt().exp);
                p = mpolySub(p, mpolyMulTerm(g, qCoeff, qExp), order);
                divided = true;
                break;
            }
        }
        if (!divided) {
            rOut.terms.push_back(ltP);
            p.terms.remove_at(0);
        }
    }
    return true;
}

bool exprToMPolyRec(const Ctx &c, Expr e, keel::ArrayRef<Expr> vars,
                    MonomialOrder order, MPoly &out)
{
    if (e.isNull())
        return false;
    const keel::usize k = vars.size();
    switch (c.kind(e)) {
    case NodeKind::Number: {
        out.terms.clear();
        const Rational &r = c.numberValue(e);
        if (!r.isZero())
            out.terms.push_back(MTerm{r, keel::Array<keel::i32>(k, 0)});
        return true;
    }
    case NodeKind::Symbol: {
        for (keel::usize i = 0; i < k; ++i) {
            if (e == vars[i]) {
                out.terms.clear();
                keel::Array<keel::i32> exp(k, 0);
                exp[i] = 1;
                out.terms.push_back(MTerm{Rational(keel::i64{1}), std::move(exp)});
                return true;
            }
        }
        return false; // symbol not in vars
    }
    case NodeKind::Add: {
        MPoly acc;
        for (keel::usize i = 0; i < c.childCount(e); ++i) {
            MPoly sub;
            if (!exprToMPolyRec(c, c.child(e, i), vars, order, sub))
                return false;
            acc = mpolyAdd(acc, sub, order);
        }
        out = std::move(acc);
        return true;
    }
    case NodeKind::Mul: {
        MPoly acc;
        acc.terms.push_back(MTerm{Rational(keel::i64{1}), keel::Array<keel::i32>(k, 0)});
        for (keel::usize i = 0; i < c.childCount(e); ++i) {
            MPoly sub;
            if (!exprToMPolyRec(c, c.child(e, i), vars, order, sub))
                return false;
            acc = mpolyMul(acc, sub, order);
        }
        out = std::move(acc);
        return true;
    }
    case NodeKind::Pow: {
        const Expr base = c.child(e, 0);
        const Expr expNode = c.child(e, 1);
        if (c.kind(expNode) != NodeKind::Number ||
            !(c.numberValue(expNode).den() == BigInt(1))) {
            return false;
        }
        keel::i64 p = 0;
        if (!c.numberValue(expNode).num().fitsInt64(p) || p < 0 || p > 64)
            return false;
        MPoly bPoly;
        if (!exprToMPolyRec(c, base, vars, order, bPoly))
            return false;
        MPoly acc;
        acc.terms.push_back(MTerm{Rational(keel::i64{1}), keel::Array<keel::i32>(k, 0)});
        for (keel::i64 i = 0; i < p; ++i)
            acc = mpolyMul(acc, bPoly, order);
        out = std::move(acc);
        return true;
    }
    case NodeKind::Func:
    case NodeKind::RootOf:
        return false;
    }
    return false;
}

bool exprToMPoly(Ctx &c, Expr e, keel::ArrayRef<Expr> vars,
                 MonomialOrder order, MPoly &out)
{
    if (e.isNull())
        return false;
    const Expr expd = c.expand(e);
    if (exprToMPolyRec(c, expd, vars, order, out))
        return true;
    const Expr rat = simplifyRationalExpr(c, e);
    if (!rat.isNull()) {
        return exprToMPolyRec(c, c.expand(rat), vars, order, out);
    }
    return false;
}

Expr mpolyToExpr(Ctx &c, const MPoly &p, keel::ArrayRef<Expr> vars)
{
    if (p.isZero())
        return c.zero();
    keel::Array<Expr> addTerms;
    addTerms.reserve(p.terms.size());
    for (const MTerm &t : p.terms) {
        keel::Array<Expr> mulFacs;
        if (t.coeff != Rational(keel::i64{1}))
            mulFacs.push_back(c.number(t.coeff));
        for (keel::usize i = 0; i < vars.size(); ++i) {
            if (t.exp[i] == 1) {
                mulFacs.push_back(vars[i]);
            } else if (t.exp[i] > 1) {
                mulFacs.push_back(
                    c.pow(vars[i], c.number(keel::as<keel::i64>(t.exp[i]))));
            }
        }
        if (mulFacs.empty())
            addTerms.push_back(c.one());
        else if (mulFacs.size() == 1)
            addTerms.push_back(mulFacs[0]);
        else
            addTerms.push_back(c.mul(mulFacs));
    }
    return addTerms.size() == 1 ? addTerms[0] : c.add(addTerms);
}

} // namespace

GroebnerResult groebnerBasis(Ctx &c, keel::ArrayRef<Expr> polys,
                             keel::ArrayRef<Expr> vars,
                             MonomialOrder order, Budget *budget)
{
    GroebnerResult out;
    if (vars.empty()) {
        out.reason.assign("empty variable list");
        return out;
    }
    for (keel::usize i = 0; i < vars.size(); ++i) {
        if (vars[i].isNull() || c.kind(vars[i]) != NodeKind::Symbol) {
            out.reason.assign("all Groebner variables must be Symbol nodes");
            return out;
        }
        for (keel::usize j = i + 1; j < vars.size(); ++j) {
            if (vars[i] == vars[j]) {
                out.reason.assign("duplicate variable in Groebner variable list");
                return out;
            }
        }
    }
    if (!checkGroebnerBudget(c, budget, out.reason))
        return out;

    keel::Array<MPoly> F;
    keel::Array<MPoly> G;
    for (const Expr &pe : polys) {
        if (pe.isNull()) {
            out.reason.assign("null polynomial in input list");
            return out;
        }
        MPoly mp;
        if (!exprToMPoly(c, pe, vars, order, mp)) {
            out.reason.assign("input expression is not a polynomial in Q[vars]");
            return out;
        }
        if (!mp.isZero()) {
            mpolyMakeMonic(mp);
            F.push_back(mp);
            G.push_back(std::move(mp));
        }
    }

    if (G.empty()) {
        out.basis = {c.zero()};
        out.status = GroebnerResult::Status::ProvedSymbolic;
        return out;
    }

    // Critical pairs (i, j) with 0 <= i < j < G.size()
    struct Pair {
        keel::usize i;
        keel::usize j;
        keel::i32 lcmDeg;
    };
    keel::Array<Pair> pairs;
    for (keel::usize i = 0; i < G.size(); ++i) {
        for (keel::usize j = i + 1; j < G.size(); ++j) {
            const keel::i32 d = totalDegree(monomialLcm(G[i].lt().exp, G[j].lt().exp));
            pairs.push_back(Pair{i, j, d});
        }
    }

    constexpr keel::usize kMaxBasisSize = 96;
    while (!pairs.empty()) {
        if (!checkGroebnerBudget(c, budget, out.reason))
            return out;

        // Normal selection strategy: pick critical pair with smallest total degree of lcm(LM(g_i), LM(g_j)).
        auto bestIt = std::min_element(
            pairs.begin(), pairs.end(),
            [](const Pair &a, const Pair &b) { return a.lcmDeg < b.lcmDeg; });
        const Pair cur = *bestIt;
        pairs.remove_at(keel::as<keel::usize>(bestIt - pairs.begin()));

        const MPoly &gi = G[cur.i];
        const MPoly &gj = G[cur.j];
        // Buchberger's first criterion: coprime leading monomials reduce to 0.
        if (monomialsCoprime(gi.lt().exp, gj.lt().exp))
            continue;

        const MPoly s = mpolySPoly(gi, gj, order);
        if (s.isZero())
            continue;

        MPoly rem;
        if (!mpolyReduce(c, s, G, order, budget, rem, out.reason))
            return out;
        if (rem.isZero())
            continue;

        mpolyMakeMonic(rem);
        // If rem is a non-zero constant (1), the ideal is the unit ideal <1>.
        if (totalDegree(rem.lt().exp) == 0) {
            G.clear();
            G.push_back(std::move(rem));
            pairs.clear();
            break;
        }

        if (G.size() >= kMaxBasisSize) {
            out.reason.assign("Groebner basis size limit exceeded");
            return out;
        }
        const keel::usize newIdx = G.size();
        for (keel::usize i = 0; i < newIdx; ++i) {
            const keel::i32 d =
                totalDegree(monomialLcm(G[i].lt().exp, rem.lt().exp));
            pairs.push_back(Pair{i, newIdx, d});
        }
        G.push_back(std::move(rem));
    }

    // Minimalize the Groebner basis: remove any g_i whose LM is divisible by LM(g_j) (j != i).
    keel::Array<MPoly> minimal;
    for (keel::usize i = 0; i < G.size(); ++i) {
        if (G[i].isZero())
            continue;
        bool redundant = false;
        for (keel::usize j = 0; j < G.size(); ++j) {
            if (i == j || G[j].isZero())
                continue;
            if (G[i].lt().exp == G[j].lt().exp) {
                if (j < i) {
                    redundant = true;
                    break;
                }
            } else if (monomialDivides(G[j].lt().exp, G[i].lt().exp)) {
                redundant = true;
                break;
            }
        }
        if (!redundant)
            minimal.push_back(G[i]);
    }

    // Interreduce to obtain the unique monic reduced Groebner basis.
    for (keel::usize i = 0; i < minimal.size(); ++i) {
        keel::Array<MPoly> others;
        others.reserve(minimal.size() - 1);
        for (keel::usize j = 0; j < minimal.size(); ++j) {
            if (j != i)
                others.push_back(minimal[j]);
        }
        MPoly red;
        if (!mpolyReduce(c, minimal[i], others, order, budget, red, out.reason))
            return out;
        mpolyMakeMonic(red);
        minimal[i] = std::move(red);
    }

    // Sort in ascending leading-monomial order (so in Lex order, the univariate
    // elimination polynomial in vars.back() comes first).
    std::sort(minimal.begin(), minimal.end(),
              [&](const MPoly &a, const MPoly &b) {
                  return compareMonomial(a.lt().exp, b.lt().exp, order) < 0;
              });

    // Proof-carrying certificate:
    //   1) Every input polynomial f in F reduces to 0 modulo `minimal`.
    //   2) Buchberger's criterion: every S-polynomial S(g_i, g_j) reduces to 0 modulo `minimal`.
    for (const MPoly &f : F) {
        MPoly r;
        if (!mpolyReduce(c, f, minimal, order, budget, r, out.reason) ||
            !r.isZero()) {
            out.reason.assign("input generator failed Groebner ideal membership certificate");
            return out;
        }
    }
    for (keel::usize i = 0; i < minimal.size(); ++i) {
        for (keel::usize j = i + 1; j < minimal.size(); ++j) {
            if (monomialsCoprime(minimal[i].lt().exp, minimal[j].lt().exp))
                continue;
            const MPoly s = mpolySPoly(minimal[i], minimal[j], order);
            MPoly r;
            if (!mpolyReduce(c, s, minimal, order, budget, r, out.reason) ||
                !r.isZero()) {
                out.reason.assign("basis failed Buchberger S-polynomial certificate");
                return out;
            }
        }
    }

    out.basis.reserve(minimal.size());
    for (const MPoly &g : minimal)
        out.basis.push_back(mpolyToExpr(c, g, vars));
    out.status = GroebnerResult::Status::ProvedSymbolic;
    return out;
}

Expr polyReduceMulti(Ctx &c, Expr f, keel::ArrayRef<Expr> G,
                     keel::ArrayRef<Expr> vars, MonomialOrder order,
                     Budget *budget)
{
    if (f.isNull() || vars.empty())
        return Expr{};
    for (const Expr &v : vars) {
        if (v.isNull() || c.kind(v) != NodeKind::Symbol)
            return Expr{};
    }
    MPoly mf;
    if (!exprToMPoly(c, f, vars, order, mf))
        return Expr{};
    keel::Array<MPoly> mG;
    mG.reserve(G.size());
    for (const Expr &ge : G) {
        if (ge.isNull())
            return Expr{};
        MPoly mg;
        if (!exprToMPoly(c, ge, vars, order, mg))
            return Expr{};
        if (!mg.isZero())
            mG.push_back(std::move(mg));
    }
    MPoly rem;
    keel::String reason;
    if (!mpolyReduce(c, mf, mG, order, budget, rem, reason))
        return Expr{};
    return mpolyToExpr(c, rem, vars);
}

// ============================================================================
// Multivariate Exact Division, GCD (`gcdMulti`), and Factorization (`factorMulti`)
// ============================================================================

namespace {

void collectPolyVarsRec(const Ctx &c, Expr e, keel::Array<Expr> &vars)
{
    if (e.isNull())
        return;
    if (c.kind(e) == NodeKind::Symbol) {
        if (std::find(vars.begin(), vars.end(), e) == vars.end())
            vars.push_back(e);
        return;
    }
    for (keel::usize i = 0; i < c.childCount(e); ++i)
        collectPolyVarsRec(c, c.child(e, i), vars);
}

keel::Array<Expr> resolvePolyVars(const Ctx &c,
                                  keel::ArrayRef<Expr> exprs,
                                  keel::ArrayRef<Expr> userVars)
{
    if (!userVars.empty())
        return keel::Array<Expr>::from(userVars);
    keel::Array<Expr> vars;
    for (const Expr &e : exprs)
        collectPolyVarsRec(c, e, vars);
    std::sort(vars.begin(), vars.end(),
              [&](Expr a, Expr b) { return c.compare(a, b) < 0; });
    return vars;
}

MPoly mpolyConst(const Rational &r, keel::usize kVars)
{
    MPoly out;
    if (!r.isZero())
        out.terms.push_back(MTerm{r, keel::Array<keel::i32>(kVars, 0)});
    return out;
}

bool mpolyIsConstant(const MPoly &p)
{
    if (p.isZero())
        return true;
    return p.terms.size() == 1 && totalDegree(p.terms[0].exp) == 0;
}

keel::i32 mpolyDegInVar(const MPoly &p, keel::usize varIdx)
{
    keel::i32 d = 0;
    for (const MTerm &t : p.terms) {
        if (t.exp[varIdx] > d)
            d = t.exp[varIdx];
    }
    return d;
}

keel::Array<keel::i32> mpolyMinMonomial(const MPoly &p, keel::usize kVars)
{
    keel::Array<keel::i32> minExp(kVars, 0);
    if (p.isZero())
        return minExp;
    minExp = p.terms[0].exp.clone();
    for (keel::usize i = 1; i < p.terms.size(); ++i) {
        for (keel::usize j = 0; j < kVars; ++j)
            minExp[j] = std::min(minExp[j], p.terms[i].exp[j]);
    }
    return minExp;
}

MPoly mpolyShiftMonomial(const MPoly &p, const keel::Array<keel::i32> &shift)
{
    MPoly out = p;
    for (MTerm &t : out.terms) {
        for (keel::usize j = 0; j < shift.size(); ++j)
            t.exp[j] += shift[j];
    }
    return out;
}

// Exact division in Q[x_1, ..., x_k]: returns true iff `a == b * qOut`.
bool mpolyDivExact(const MPoly &a, const MPoly &b, MonomialOrder order,
                   MPoly &qOut)
{
    if (b.isZero()) {
        qOut.terms.clear();
        return false;
    }
    if (a.isZero()) {
        qOut.terms.clear();
        return true;
    }

    MPoly p = a;
    const MPoly divisor = b;
    qOut.terms.clear();
    const keel::usize maxSteps = p.terms.size() * 8 + 64;
    keel::usize steps = 0;
    while (!p.isZero()) {
        if (++steps > maxSteps)
            return false;
        const MTerm ltP = p.lt();
        const MTerm ltB = divisor.lt();
        if (!monomialDivides(ltB.exp, ltP.exp))
            return false;
        const Rational qCoeff = ltP.coeff / ltB.coeff;
        const keel::Array<keel::i32> qExp = monomialSub(ltP.exp, ltB.exp);
        qOut.terms.push_back(MTerm{qCoeff, qExp.clone()});
        p = mpolySub(p, mpolyMulTerm(divisor, qCoeff, qExp), order);
    }
    normalizeMPoly(qOut, order);
    return true;
}

MPoly mpolyDiffInVar(const MPoly &p, keel::usize varIdx, MonomialOrder order)
{
    MPoly out;
    for (const MTerm &t : p.terms) {
        const keel::i32 e = t.exp[varIdx];
        if (e > 0) {
            keel::Array<keel::i32> nExp = t.exp.clone();
            nExp[varIdx] = e - 1;
            out.terms.push_back(
                MTerm{t.coeff * Rational(keel::as<keel::i64>(e)),
                      std::move(nExp)});
        }
    }
    normalizeMPoly(out, order);
    return out;
}

keel::Array<MPoly> mpolyDecomposeInVar(const MPoly &p, keel::usize varIdx,
                                       keel::usize kVars, MonomialOrder order)
{
    const keel::i32 d = mpolyDegInVar(p, varIdx);
    keel::Array<MPoly> coeffs(d + 1);
    for (const MTerm &t : p.terms) {
        const keel::i32 e = t.exp[varIdx];
        keel::Array<keel::i32> cExp = t.exp.clone();
        cExp[varIdx] = 0;
        coeffs[keel::as<keel::usize>(e)].terms.push_back(
            MTerm{t.coeff, std::move(cExp)});
    }
    for (MPoly &cPoly : coeffs)
        normalizeMPoly(cPoly, order);
    (void)kVars;
    return coeffs;
}

MPoly mpolyComposeInVar(const keel::Array<MPoly> &coeffs, keel::usize varIdx,
                        MonomialOrder order)
{
    MPoly out;
    for (keel::usize d = 0; d < coeffs.size(); ++d) {
        for (const MTerm &t : coeffs[d].terms) {
            keel::Array<keel::i32> nExp = t.exp.clone();
            nExp[varIdx] = keel::as<keel::i32>(d);
            out.terms.push_back(MTerm{t.coeff, std::move(nExp)});
        }
    }
    normalizeMPoly(out, order);
    return out;
}

UPoly mpolyToUPolyInVar(const MPoly &p, keel::usize varIdx)
{
    if (p.isZero())
        return UPoly{};
    const keel::i32 d = mpolyDegInVar(p, varIdx);
    keel::Array<Rational> coeffs(d + 1,
                                 Rational(keel::i64{0}));
    for (const MTerm &t : p.terms) {
        coeffs[keel::as<keel::usize>(t.exp[varIdx])] += t.coeff;
    }
    return UPoly(std::move(coeffs));
}

MPoly upolyToMPolyInVar(const UPoly &u, keel::usize varIdx, keel::usize kVars,
                        MonomialOrder order)
{
    MPoly out;
    if (u.isZero())
        return out;
    for (keel::i32 d = 0; d <= u.deg(); ++d) {
        const Rational c = u.coeff(d);
        if (!c.isZero()) {
            keel::Array<keel::i32> exp(kVars, 0);
            exp[varIdx] = d;
            out.terms.push_back(MTerm{c, std::move(exp)});
        }
    }
    normalizeMPoly(out, order);
    return out;
}

MPoly mpolyGcdRec(const MPoly &a, const MPoly &b, keel::usize kVars,
                  MonomialOrder order, Budget *budget);

MPoly mpolyContentInVar(const MPoly &p, keel::usize varIdx, keel::usize kVars,
                        MonomialOrder order, Budget *budget)
{
    if (p.isZero())
        return MPoly{};
    const keel::Array<MPoly> coeffs =
        mpolyDecomposeInVar(p, varIdx, kVars, order);
    MPoly g;
    for (const MPoly &cPoly : coeffs) {
        if (cPoly.isZero())
            continue;
        if (g.isZero())
            g = cPoly;
        else
            g = mpolyGcdRec(g, cPoly, kVars, order, budget);
        if (mpolyIsConstant(g)) {
            return mpolyConst(Rational(keel::i64{1}), kVars);
        }
    }
    mpolyMakeMonic(g);
    return g;
}

MPoly mpolyPrimitivePartInVar(const MPoly &p, keel::usize varIdx,
                              keel::usize kVars, MonomialOrder order,
                              Budget *budget)
{
    if (p.isZero())
        return MPoly{};
    const MPoly cont = mpolyContentInVar(p, varIdx, kVars, order, budget);
    MPoly prim;
    if (!cont.isZero() && !mpolyIsConstant(cont) &&
        mpolyDivExact(p, cont, order, prim)) {
        mpolyMakeMonic(prim);
        return prim;
    }
    prim = p;
    mpolyMakeMonic(prim);
    return prim;
}

MPoly mpolyGcdRec(const MPoly &a, const MPoly &b, keel::usize kVars,
                  MonomialOrder order, Budget *budget)
{
    if (a.isZero()) {
        MPoly out = b;
        mpolyMakeMonic(out);
        return out;
    }
    if (b.isZero()) {
        MPoly out = a;
        mpolyMakeMonic(out);
        return out;
    }
    if (kVars == 0)
        return mpolyConst(Rational(keel::i64{1}), 0);

    // 1. Strip greatest common monomial factor x^gExp
    const keel::Array<keel::i32> minA = mpolyMinMonomial(a, kVars);
    const keel::Array<keel::i32> minB = mpolyMinMonomial(b, kVars);
    keel::Array<keel::i32> gExp(kVars, 0);
    keel::Array<keel::i32> negA(kVars, 0), negB(kVars, 0);
    for (keel::usize i = 0; i < kVars; ++i) {
        gExp[i] = std::min(minA[i], minB[i]);
        negA[i] = -minA[i];
        negB[i] = -minB[i];
    }

    MPoly P = mpolyShiftMonomial(a, negA);
    MPoly Q = mpolyShiftMonomial(b, negB);
    mpolyMakeMonic(P);
    mpolyMakeMonic(Q);

    auto finishWithMonomial = [&](MPoly d) -> MPoly {
        MPoly out = mpolyShiftMonomial(d, gExp);
        normalizeMPoly(out, order);
        mpolyMakeMonic(out);
        return out;
    };

    if (mpolyIsConstant(P) || mpolyIsConstant(Q))
        return finishWithMonomial(mpolyConst(Rational(keel::i64{1}), kVars));

    MPoly qTmp;
    if (mpolyDivExact(Q, P, order, qTmp))
        return finishWithMonomial(P);
    if (mpolyDivExact(P, Q, order, qTmp))
        return finishWithMonomial(Q);

    // 2. Inspect active variables
    keel::Array<keel::usize> activeVars;
    for (keel::usize i = 0; i < kVars; ++i) {
        const keel::i32 da = mpolyDegInVar(P, i);
        const keel::i32 db = mpolyDegInVar(Q, i);
        if (da > 0 && db == 0) {
            // Variable `i` appears in P but not in Q: gcd(P, Q) = gcd(cont_i(P), Q)
            const MPoly contP = mpolyContentInVar(P, i, kVars, order, budget);
            return finishWithMonomial(
                mpolyGcdRec(contP, Q, kVars, order, budget));
        }
        if (db > 0 && da == 0) {
            const MPoly contQ = mpolyContentInVar(Q, i, kVars, order, budget);
            return finishWithMonomial(
                mpolyGcdRec(P, contQ, kVars, order, budget));
        }
        if (da > 0 || db > 0)
            activeVars.push_back(i);
    }

    if (activeVars.empty())
        return finishWithMonomial(mpolyConst(Rational(keel::i64{1}), kVars));

    // Base case: univariate in `activeVars[0]`
    if (activeVars.size() == 1) {
        const keel::usize v = activeVars[0];
        const UPoly uP = mpolyToUPolyInVar(P, v);
        const UPoly uQ = mpolyToUPolyInVar(Q, v);
        const UPoly uG = UPoly::gcd(uP, uQ);
        return finishWithMonomial(upolyToMPolyInVar(uG, v, kVars, order));
    }

    // 3. Pick active variable `mainVar` of smallest positive max-degree
    keel::usize mainVar = activeVars[0];
    keel::i32 bestMaxDeg =
        std::max(mpolyDegInVar(P, mainVar), mpolyDegInVar(Q, mainVar));
    keel::i32 bestSumDeg =
        mpolyDegInVar(P, mainVar) + mpolyDegInVar(Q, mainVar);
    for (keel::usize idx = 1; idx < activeVars.size(); ++idx) {
        const keel::usize v = activeVars[idx];
        const keel::i32 mx = std::max(mpolyDegInVar(P, v), mpolyDegInVar(Q, v));
        const keel::i32 sm = mpolyDegInVar(P, v) + mpolyDegInVar(Q, v);
        if (mx < bestMaxDeg || (mx == bestMaxDeg && sm < bestSumDeg)) {
            mainVar = v;
            bestMaxDeg = mx;
            bestSumDeg = sm;
        }
    }

    const MPoly contP = mpolyContentInVar(P, mainVar, kVars, order, budget);
    const MPoly contQ = mpolyContentInVar(Q, mainVar, kVars, order, budget);
    const MPoly contG = mpolyGcdRec(contP, contQ, kVars, order, budget);

    if (!mpolyIsConstant(contP))
        mpolyDivExact(P, contP, order, P);
    if (!mpolyIsConstant(contQ))
        mpolyDivExact(Q, contQ, order, Q);
    mpolyMakeMonic(P);
    mpolyMakeMonic(Q);

    if (mpolyDegInVar(P, mainVar) < mpolyDegInVar(Q, mainVar))
        std::swap(P, Q);

    // Primitive Polynomial Remainder Sequence (Primitive PRS) in `mainVar`
    keel::i32 prsIter = 0;
    while (!Q.isZero() && mpolyDegInVar(Q, mainVar) > 0 && ++prsIter <= 64) {
        if (budget && !budget->step())
            break;
        if (mpolyDivExact(P, Q, order, qTmp)) {
            P = Q;
            break;
        }
        const keel::Array<MPoly> qCoeffs =
            mpolyDecomposeInVar(Q, mainVar, kVars, order);
        const keel::i32 dQ = keel::as<keel::i32>(qCoeffs.size()) - 1;
        const MPoly &lcQ = qCoeffs.back();

        MPoly R = P;
        keel::i32 subSteps = 0;
        while (!R.isZero() && mpolyDegInVar(R, mainVar) >= dQ &&
               ++subSteps <= 64) {
            const keel::Array<MPoly> rCoeffs =
                mpolyDecomposeInVar(R, mainVar, kVars, order);
            const keel::i32 dR = keel::as<keel::i32>(rCoeffs.size()) - 1;
            const MPoly &lcR = rCoeffs.back();

            // Cancel common factor between lcR and lcQ before cross-multiplying
            const MPoly gLc = mpolyGcdRec(lcR, lcQ, kVars, order, budget);
            MPoly mulR = lcQ;
            MPoly mulQ = lcR;
            if (!mpolyIsConstant(gLc)) {
                mpolyDivExact(lcQ, gLc, order, mulR);
                mpolyDivExact(lcR, gLc, order, mulQ);
            }
            keel::Array<keel::i32> shiftExp(kVars, 0);
            shiftExp[mainVar] = dR - dQ;
            const MPoly shiftedQ = mpolyShiftMonomial(Q, shiftExp);
            R = mpolySub(mpolyMul(mulR, R, order),
                         mpolyMul(mulQ, shiftedQ, order), order);
        }

        if (R.isZero()) {
            P = Q;
            break;
        }
        if (mpolyDegInVar(R, mainVar) == 0) {
            // Coprime in mainVar
            P = mpolyConst(Rational(keel::i64{1}), kVars);
            break;
        }
        R = mpolyPrimitivePartInVar(R, mainVar, kVars, order, budget);
        P = std::move(Q);
        Q = std::move(R);
    }

    const MPoly combined = mpolyMul(contG, P, order);
    return finishWithMonomial(combined);
}

// Substitute `varIdx -> val` in `p`.
MPoly mpolyEvalVarAtRational(const MPoly &p, keel::usize varIdx,
                             const Rational &val, MonomialOrder order)
{
    MPoly out;
    for (const MTerm &t : p.terms) {
        const keel::i32 e = t.exp[varIdx];
        Rational c = t.coeff;
        if (e > 0) {
            if (val.isZero())
                continue;
            const BigInt numP =
                BigInt::powUInt(val.num(), keel::as<keel::u64>(e));
            const BigInt denP =
                BigInt::powUInt(val.den(), keel::as<keel::u64>(e));
            c = c * Rational(numP, denP);
        }
        keel::Array<keel::i32> nExp = t.exp.clone();
        nExp[varIdx] = 0;
        out.terms.push_back(MTerm{c, std::move(nExp)});
    }
    normalizeMPoly(out, order);
    return out;
}

// Shift variable `varIdx -> varIdx + shift` in `p`.
MPoly mpolyShiftVarByRational(const MPoly &p, keel::usize varIdx,
                              const Rational &shift, keel::usize kVars,
                              MonomialOrder order)
{
    if (p.isZero() || shift.isZero())
        return p;
    const keel::Array<MPoly> coeffs =
        mpolyDecomposeInVar(p, varIdx, kVars, order);
    if (coeffs.size() <= 1)
        return p;

    // Horner evaluation in (x_varIdx + shift)
    MPoly xPlusShift;
    keel::Array<keel::i32> e1(kVars, 0);
    e1[varIdx] = 1;
    xPlusShift.terms.push_back(MTerm{Rational(keel::i64{1}), keel::move(e1)});
    xPlusShift.terms.push_back(MTerm{shift, keel::Array<keel::i32>(kVars, 0)});
    normalizeMPoly(xPlusShift, order);

    MPoly acc = coeffs.back();
    for (keel::usize idx = coeffs.size() - 1; idx > 0; --idx) {
        acc = mpolyAdd(mpolyMul(acc, xPlusShift, order), coeffs[idx - 1], order);
    }
    return acc;
}

// Substitute `mainVar -> L(otherVars) * mainVar` in `p`.
MPoly mpolyScaleVarByMPoly(const MPoly &p, keel::usize mainVar, const MPoly &L,
                           keel::usize kVars, MonomialOrder order)
{
    const keel::Array<MPoly> coeffs =
        mpolyDecomposeInVar(p, mainVar, kVars, order);
    if (coeffs.size() <= 1)
        return p;
    keel::Array<MPoly> lPows(coeffs.size());
    lPows[0] = mpolyConst(Rational(keel::i64{1}), kVars);
    for (keel::usize i = 1; i < coeffs.size(); ++i)
        lPows[i] = mpolyMul(lPows[i - 1], L, order);

    keel::Array<MPoly> newCoeffs(coeffs.size());
    for (keel::usize i = 0; i < coeffs.size(); ++i)
        newCoeffs[i] = mpolyMul(coeffs[i], lPows[i], order);
    return mpolyComposeInVar(newCoeffs, mainVar, order);
}

// Factor a primitive, squarefree multivariate polynomial `S` (containing no
// monomial factors) into monic irreducible factors in Q[x_1, ..., x_k].
void factorPrimitiveSquarefreeMPoly(const MPoly &S, keel::usize kVars,
                                    MonomialOrder order, Budget *budget,
                                    keel::Array<MPoly> &irredOut)
{
    if (S.isZero() || mpolyIsConstant(S))
        return;

    keel::Array<keel::usize> activeVars;
    for (keel::usize i = 0; i < kVars; ++i) {
        if (mpolyDegInVar(S, i) > 0)
            activeVars.push_back(i);
    }
    if (activeVars.empty())
        return;

    // 1. Univariate base case
    if (activeVars.size() == 1) {
        const keel::usize v = activeVars[0];
        const UPoly uS = mpolyToUPolyInVar(S, v);
        const keel::Array<UPoly> uFacs = factorOverQ(uS, budget);
        for (const UPoly &uf : uFacs) {
            if (uf.deg() > 0) {
                MPoly mf = upolyToMPolyInVar(uf, v, kVars, order);
                mpolyMakeMonic(mf);
                irredOut.push_back(std::move(mf));
            }
        }
        return;
    }

    // 2. Pick active variable `mainVar` of minimum positive degree
    keel::usize mainVar = activeVars[0];
    keel::i32 minDeg = mpolyDegInVar(S, mainVar);
    for (keel::usize idx = 1; idx < activeVars.size(); ++idx) {
        const keel::i32 d = mpolyDegInVar(S, activeVars[idx]);
        if (d < minDeg) {
            minDeg = d;
            mainVar = activeVars[idx];
        }
    }

    // Since S is primitive in every active variable, if minDeg == 1 then S is
    // linear in `mainVar` with coprime coefficients, hence provably irreducible!
    if (minDeg == 1) {
        MPoly mS = S;
        mpolyMakeMonic(mS);
        irredOut.push_back(std::move(mS));
        return;
    }

    keel::Array<keel::usize> otherVars;
    for (keel::usize v : activeVars) {
        if (v != mainVar)
            otherVars.push_back(v);
    }

    // 3. Gauss monic transformation in `mainVar`:
    //    S(x, y) = sum_{i=0}^d A_i(y) * x^i,  L(y) = A_d(y)
    //    S_monic(X, y) = X^d + sum_{i=0}^{d-1} A_i(y) * L(y)^(d - 1 - i) * X^i
    MPoly curS = S;
    mpolyMakeMonic(curS);

    const keel::Array<MPoly> sCoeffs =
        mpolyDecomposeInVar(curS, mainVar, kVars, order);
    const keel::i32 dX = keel::as<keel::i32>(sCoeffs.size()) - 1;
    const MPoly L = sCoeffs.back();

    keel::Array<MPoly> lPows(dX);
    lPows[0] = mpolyConst(Rational(keel::i64{1}), kVars);
    for (keel::i32 i = 1; i < dX; ++i) {
        lPows[keel::as<keel::usize>(i)] =
            mpolyMul(lPows[keel::as<keel::usize>(i - 1)], L, order);
    }

    keel::Array<MPoly> monicCoeffs(dX + 1);
    monicCoeffs[keel::as<keel::usize>(dX)] =
        mpolyConst(Rational(keel::i64{1}), kVars);
    for (keel::i32 i = 0; i < dX; ++i) {
        monicCoeffs[keel::as<keel::usize>(i)] =
            mpolyMul(sCoeffs[keel::as<keel::usize>(i)],
                     lPows[keel::as<keel::usize>(dX - 1 - i)], order);
    }
    const MPoly sMonic = mpolyComposeInVar(monicCoeffs, mainVar, order);

    // 4. Find a small integer evaluation point `b` for `otherVars` such that
    //    L(b) != 0 and s0(X) = sMonic(X, b) is squarefree of degree dX.
    static const keel::i32 kCandCoords[] = {0, 1, -1, 2, -2, 3, -3, 4, 5};
    keel::Array<Rational> evalPt(otherVars.size(), Rational(keel::i64{0}));
    UPoly s0;
    bool foundPt = false;
    for (keel::i32 trial = 0; trial < 45 && !foundPt; ++trial) {
        keel::i32 code = trial;
        for (keel::usize j = 0; j < otherVars.size(); ++j) {
            evalPt[j] = Rational(
                keel::as<keel::i64>(kCandCoords[code % 9]));
            code /= 9;
        }
        MPoly lEval = L;
        MPoly smEval = sMonic;
        for (keel::usize j = 0; j < otherVars.size(); ++j) {
            lEval = mpolyEvalVarAtRational(lEval, otherVars[j], evalPt[j], order);
            smEval =
                mpolyEvalVarAtRational(smEval, otherVars[j], evalPt[j], order);
        }
        if (lEval.isZero())
            continue;
        const UPoly candS0 = mpolyToUPolyInVar(smEval, mainVar);
        if (candS0.deg() != dX)
            continue;
        const UPoly g0 = UPoly::gcd(candS0, candS0.derivative());
        if (g0.deg() == 0) {
            s0 = candS0;
            foundPt = true;
        }
    }

    if (!foundPt) {
        irredOut.push_back(curS);
        return;
    }

    keel::Array<UPoly> uFactors = factorOverQ(s0, budget);
    if (uFactors.size() <= 1) {
        // Irreducible specialization => S is irreducible over Q[vars]
        irredOut.push_back(curS);
        return;
    }

    // 5. Shift `otherVars`: y_j -> u_j + evalPt[j] so the expansion point is u = 0.
    MPoly sShifted = sMonic;
    for (keel::usize j = 0; j < otherVars.size(); ++j) {
        sShifted = mpolyShiftVarByRational(sShifted, otherVars[j], evalPt[j],
                                           kVars, order);
    }

    auto otherTotalDeg = [&](const keel::Array<keel::i32> &exp) -> keel::i32 {
        keel::i32 d = 0;
        for (keel::usize v : otherVars)
            d += exp[v];
        return d;
    };

    keel::i32 maxOtherDeg = 0;
    for (const MTerm &t : sShifted.terms)
        maxOtherDeg = std::max(maxOtherDeg, otherTotalDeg(t.exp));

    // Try lifting singletons first, then pairs if needed, via Multivariate Total-Degree Hensel Lifting
    for (keel::usize subSize = 1; subSize <= uFactors.size() / 2; ++subSize) {
        if (uFactors.size() <= 1)
            break;
        keel::Array<bool> mask(uFactors.size(), false);
        std::fill(mask.begin(),
                  mask.begin() + keel::as<keel::isize>(subSize), true);

        bool factorFoundInPass = false;
        do {
            UPoly g0({Rational(keel::i64{1})});
            UPoly h0({Rational(keel::i64{1})});
            for (keel::usize i = 0; i < uFactors.size(); ++i) {
                if (mask[i])
                    g0 = g0 * uFactors[i];
                else
                    h0 = h0 * uFactors[i];
            }
            g0.makeMonic();
            h0.makeMonic();

            if (UPoly::gcd(g0, h0).deg() != 0)
                continue;
            const UPoly B = UPoly::invMod(h0, g0);
            UPoly A;
            UPoly remBezout;
            UPoly::divMod(UPoly(Rational(keel::i64{1})) - B * h0, g0, A,
                          remBezout);

            MPoly gLift = upolyToMPolyInVar(g0, mainVar, kVars, order);
            MPoly hLift = upolyToMPolyInVar(h0, mainVar, kVars, order);

            for (keel::i32 degU = 1; degU <= maxOtherDeg; ++degU) {
                const MPoly err =
                    mpolySub(sShifted, mpolyMul(gLift, hLift, order), order);
                if (err.isZero())
                    break;

                // Group terms of `err` that have total degree `degU` in `otherVars`
                // by their `otherVars` exponent vector.
                struct Bucket
                {
                    keel::Array<keel::i32> uExp;
                    keel::Array<Rational> coeffs;
                };
                keel::Array<Bucket> buckets;
                for (const MTerm &t : err.terms) {
                    if (otherTotalDeg(t.exp) != degU)
                        continue;
                    keel::Array<keel::i32> uExp = t.exp.clone();
                    uExp[mainVar] = 0;
                    Bucket *found = nullptr;
                    for (Bucket &b : buckets) {
                        if (b.uExp == uExp) {
                            found = &b;
                            break;
                        }
                    }
                    if (!found) {
                        buckets.push_back(Bucket{keel::move(uExp), {}});
                        found = &buckets.back();
                    }
                    auto &vec = found->coeffs;
                    const keel::i32 xExp = t.exp[mainVar];
                    if (keel::as<keel::i32>(vec.size()) <= xExp)
                        vec.resize(xExp + 1,
                                   Rational(keel::i64{0}));
                    vec[keel::as<keel::usize>(xExp)] += t.coeff;
                }
                keel::sort(buckets, [](const Bucket &a, const Bucket &b) {
                    for (keel::usize i = 0; i < a.uExp.size() && i < b.uExp.size(); ++i)
                        if (a.uExp[i] != b.uExp[i])
                            return a.uExp[i] < b.uExp[i];
                    return a.uExp.size() < b.uExp.size();
                });

                for (const Bucket &kv : buckets) {
                    const keel::Array<keel::i32> &uExp = kv.uExp;
                    const UPoly eAlpha(kv.coeffs.clone());
                    if (eAlpha.isZero())
                        continue;
                    UPoly qAlpha;
                    UPoly rAlpha;
                    UPoly::divMod(B * eAlpha, g0, qAlpha, rAlpha);
                    const UPoly dhAlpha = A * eAlpha + qAlpha * h0;

                    if (!rAlpha.isZero()) {
                        const MPoly dgM =
                            upolyToMPolyInVar(rAlpha, mainVar, kVars, order);
                        gLift = mpolyAdd(
                            gLift,
                            mpolyMulTerm(dgM, Rational(keel::i64{1}), uExp),
                            order);
                    }
                    if (!dhAlpha.isZero()) {
                        const MPoly dhM =
                            upolyToMPolyInVar(dhAlpha, mainVar, kVars, order);
                        hLift = mpolyAdd(
                            hLift,
                            mpolyMulTerm(dhM, Rational(keel::i64{1}), uExp),
                            order);
                    }
                }
            }

            // Unshift `otherVars`: u_j -> y_j - evalPt[j]
            MPoly gUnshifted = gLift;
            for (keel::usize j = 0; j < otherVars.size(); ++j) {
                gUnshifted = mpolyShiftVarByRational(
                    gUnshifted, otherVars[j], -evalPt[j], kVars, order);
            }
            // Undo Gauss monic scaling: X -> L(y) * x_main
            MPoly gScaled =
                mpolyScaleVarByMPoly(gUnshifted, mainVar, L, kVars, order);
            MPoly gCand =
                mpolyPrimitivePartInVar(gScaled, mainVar, kVars, order, budget);
            for (keel::usize v : otherVars) {
                gCand =
                    mpolyPrimitivePartInVar(gCand, v, kVars, order, budget);
            }
            mpolyMakeMonic(gCand);

            MPoly qCand;
            if (!mpolyIsConstant(gCand) &&
                mpolyDivExact(curS, gCand, order, qCand)) {
                irredOut.push_back(std::move(gCand));
                mpolyMakeMonic(qCand);
                factorPrimitiveSquarefreeMPoly(qCand, kVars, order, budget,
                                               irredOut);
                return;
            }
        } while (!factorFoundInPass &&
                 std::prev_permutation(mask.begin(), mask.end()));
    }

    irredOut.push_back(curS);
}

void factorArbitraryMPolyRec(const MPoly &P, keel::i32 mult, keel::usize kVars,
                             MonomialOrder order, Budget *budget,
                             keel::Array<std::pair<MPoly, keel::i32>> &factorsOut)
{
    if (P.isZero() || mpolyIsConstant(P))
        return;

    // 1. Strip monomial powers x_i^{m_i}
    const keel::Array<keel::i32> minExp = mpolyMinMonomial(P, kVars);
    keel::Array<keel::i32> negMin(kVars, 0);
    for (keel::usize i = 0; i < kVars; ++i) {
        if (minExp[i] > 0) {
            MPoly varPoly;
            keel::Array<keel::i32> vExp(kVars, 0);
            vExp[i] = 1;
            varPoly.terms.push_back(
                MTerm{Rational(keel::i64{1}), std::move(vExp)});
            factorsOut.emplace_back(std::move(varPoly), mult * minExp[i]);
        }
        negMin[i] = -minExp[i];
    }

    MPoly cur = mpolyShiftMonomial(P, negMin);
    mpolyMakeMonic(cur);
    if (mpolyIsConstant(cur))
        return;

    // 2. Make `cur` primitive in every active variable by factoring out contents
    for (keel::usize i = 0; i < kVars; ++i) {
        if (mpolyDegInVar(cur, i) > 0) {
            const MPoly cont =
                mpolyContentInVar(cur, i, kVars, order, budget);
            if (!cont.isZero() && !mpolyIsConstant(cont)) {
                MPoly prim;
                if (mpolyDivExact(cur, cont, order, prim)) {
                    cur = std::move(prim);
                    mpolyMakeMonic(cur);
                    factorArbitraryMPolyRec(cont, mult, kVars, order, budget,
                                            factorsOut);
                }
            }
        }
    }
    if (mpolyIsConstant(cur))
        return;

    // 3. Squarefree decomposition in the first active variable `v0`
    keel::usize v0 = 0;
    for (keel::usize i = 0; i < kVars; ++i) {
        if (mpolyDegInVar(cur, i) > 0) {
            v0 = i;
            break;
        }
    }

    const MPoly dCur = mpolyDiffInVar(cur, v0, order);
    const MPoly gSq = mpolyGcdRec(cur, dCur, kVars, order, budget);
    if (!gSq.isZero() && !mpolyIsConstant(gSq)) {
        MPoly rad;
        if (mpolyDivExact(cur, gSq, order, rad)) {
            // Factor `gSq` and `rad` via gcd(rad, gSq)
            const MPoly common = mpolyGcdRec(rad, gSq, kVars, order, budget);
            MPoly mult1Part = rad;
            MPoly higherPart = gSq;
            if (!common.isZero() && !mpolyIsConstant(common)) {
                mpolyDivExact(rad, common, order, mult1Part);
                mpolyDivExact(gSq, common, order, higherPart);
                factorArbitraryMPolyRec(common, mult + 1, kVars, order, budget,
                                        factorsOut);
                if (!mpolyIsConstant(higherPart)) {
                    factorArbitraryMPolyRec(higherPart, mult, kVars, order,
                                            budget, factorsOut);
                }
            } else {
                factorArbitraryMPolyRec(gSq, mult, kVars, order, budget,
                                        factorsOut);
            }
            cur = std::move(mult1Part);
            mpolyMakeMonic(cur);
        }
    }

    if (mpolyIsConstant(cur))
        return;

    // 4. `cur` is now primitive in all variables and squarefree
    keel::Array<MPoly> irreds;
    factorPrimitiveSquarefreeMPoly(cur, kVars, order, budget, irreds);
    for (MPoly &ir : irreds) {
        mpolyMakeMonic(ir);
        if (!mpolyIsConstant(ir))
            factorsOut.emplace_back(std::move(ir), mult);
    }
}

} // namespace

Expr divExactMulti(Ctx &c, Expr f, Expr g, keel::ArrayRef<Expr> vars,
                   Budget *budget)
{
    if (f.isNull() || g.isNull())
        return Expr{};
    const keel::Array<Expr> allVars = resolvePolyVars(c, {f, g}, vars);
    const MonomialOrder order = MonomialOrder::Lex;
    MPoly mf, mg;
    if (!exprToMPoly(c, f, allVars, order, mf) ||
        !exprToMPoly(c, g, allVars, order, mg))
        return Expr{};
    if (budget && !budget->step())
        return Expr{};
    MPoly mq;
    if (!mpolyDivExact(mf, mg, order, mq))
        return Expr{};
    return mpolyToExpr(c, mq, allVars);
}

Expr gcdMulti(Ctx &c, Expr f, Expr g, keel::ArrayRef<Expr> vars,
              Budget *budget)
{
    if (f.isNull() || g.isNull())
        return Expr{};
    const keel::Array<Expr> allVars = resolvePolyVars(c, {f, g}, vars);
    const MonomialOrder order = MonomialOrder::Lex;
    MPoly mf, mg;
    if (!exprToMPoly(c, f, allVars, order, mf) ||
        !exprToMPoly(c, g, allVars, order, mg))
        return Expr{};
    if (mf.isZero() && mg.isZero())
        return c.zero();

    MPoly md = mpolyGcdRec(mf, mg, allVars.size(), order, budget);
    mpolyMakeMonic(md);

    // Proof-carrying divisibility certificate: f = d * q_f and g = d * q_g
    MPoly qf, qg;
    if (!mpolyDivExact(mf, md, order, qf) ||
        !mpolyDivExact(mg, md, order, qg)) {
        return c.one();
    }
    return mpolyToExpr(c, md, allVars);
}

FactorMultiResult factorMulti(Ctx &c, Expr f, keel::ArrayRef<Expr> vars,
                              Budget *budget)
{
    FactorMultiResult out;
    if (f.isNull()) {
        out.reason.assign("null input expression");
        return out;
    }
    const keel::Array<Expr> allVars = resolvePolyVars(c, {f}, vars);
    const MonomialOrder order = MonomialOrder::Lex;
    MPoly mf;
    if (!exprToMPoly(c, f, allVars, order, mf)) {
        out.reason.assign("input is not a polynomial in Q[vars]");
        return out;
    }

    if (mf.isZero()) {
        out.status = FactorMultiResult::Status::ProvedSymbolic;
        out.content = Rational(keel::i64{0});
        out.expr = c.zero();
        return out;
    }

    if (mpolyIsConstant(mf)) {
        out.status = FactorMultiResult::Status::ProvedSymbolic;
        out.content = mf.lt().coeff;
        out.expr = c.number(out.content);
        return out;
    }

    keel::Array<std::pair<MPoly, keel::i32>> rawFactors;
    factorArbitraryMPolyRec(mf, 1, allVars.size(), order, budget, rawFactors);

    // Combine identical monic irreducible factors
    keel::Array<FactorMultiItem> merged;
    for (const auto &pf : rawFactors) {
        const Expr facExpr = mpolyToExpr(c, pf.first, allVars);
        bool found = false;
        for (FactorMultiItem &item : merged) {
            if (item.factor == facExpr) {
                item.multiplicity += pf.second;
                found = true;
                break;
            }
        }
        if (!found)
            merged.push_back(FactorMultiItem{facExpr, pf.second});
    }

    std::sort(merged.begin(), merged.end(),
              [&](const FactorMultiItem &a, const FactorMultiItem &b) {
                  return c.compare(a.factor, b.factor) < 0;
              });

    // Compute exact leading scalar content by comparing leading coefficients
    // of `mf` and the product of monic factors.
    MPoly prodMonic = mpolyConst(Rational(keel::i64{1}), allVars.size());
    for (const auto &pf : rawFactors) {
        for (keel::i32 m = 0; m < pf.second; ++m)
            prodMonic = mpolyMul(prodMonic, pf.first, order);
    }
    const Rational contentScalar =
        prodMonic.isZero() ? mf.lt().coeff
                           : (mf.lt().coeff / prodMonic.lt().coeff);

    keel::Array<Expr> mulParts;
    if (!(contentScalar == Rational(keel::i64{1})))
        mulParts.push_back(c.number(contentScalar));
    for (const FactorMultiItem &item : merged) {
        if (item.multiplicity == 1)
            mulParts.push_back(item.factor);
        else
            mulParts.push_back(
                c.pow(item.factor,
                      c.number(keel::as<keel::i64>(item.multiplicity))));
    }
    const Expr reconExpr =
        mulParts.empty() ? c.number(contentScalar) : c.mul(mulParts);

    // Proof-carrying identity certificate: expand(reconExpr - f) == 0
    const Expr diffCheck = c.expand(c.add({reconExpr, c.neg(f)}));
    if (!c.isZero(diffCheck)) {
        out.reason.assign("multivariate factorization failed expansion certificate");
        return out;
    }

    out.status = FactorMultiResult::Status::ProvedSymbolic;
    out.content = contentScalar;
    out.factors = std::move(merged);
    out.expr = reconExpr;
    return out;
}

} // namespace numkit::cas
