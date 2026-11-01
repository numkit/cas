// src/poly/groebner.cpp — Buchberger's algorithm for reduced Groebner bases over Q[x_1, ..., x_k].
#include <numkit/cas/poly/groebner.hpp>

#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/cas/poly/upoly.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

#include <algorithm>
#include <cstdint>
#include <map>
#include <numeric>
#include <string>
#include <utility>
#include <vector>

namespace numkit::cas {
namespace {

bool checkGroebnerBudget(const Ctx &c, Budget *budget, std::string &reason)
{
    if (!budget)
        return true;
    if (budget->step() && budget->recordArenaBytes(c.nodeCount() * 32))
        return true;
    reason = budget->status() == BudgetStatus::StepExhausted
                 ? "step budget exhausted"
                 : "arena byte budget exhausted";
    return false;
}

struct MTerm
{
    Rational coeff;
    std::vector<int> exp; // exponents of vars[0..k-1]
};

int totalDegree(const std::vector<int> &a)
{
    int s = 0;
    for (int e : a)
        s += e;
    return s;
}

// Return > 0 if monomial `a` > `b` under `order`, < 0 if `a` < `b`, 0 if `a == b`.
int compareMonomial(const std::vector<int> &a, const std::vector<int> &b,
                    MonomialOrder order)
{
    const std::size_t k = a.size();
    if (order == MonomialOrder::Lex) {
        for (std::size_t i = 0; i < k; ++i) {
            if (a[i] != b[i])
                return (a[i] > b[i]) ? 1 : -1;
        }
        return 0;
    }
    // GrevLex: compare total degree first; break ties by the LAST variable
    // where exponents differ (smaller exponent in the last variable wins).
    const int da = totalDegree(a);
    const int db = totalDegree(b);
    if (da != db)
        return (da > db) ? 1 : -1;
    for (std::size_t idx = k; idx > 0; --idx) {
        const std::size_t i = idx - 1;
        if (a[i] != b[i])
            return (a[i] < b[i]) ? 1 : -1;
    }
    return 0;
}

bool monomialDivides(const std::vector<int> &divisor,
                     const std::vector<int> &target)
{
    for (std::size_t i = 0; i < divisor.size(); ++i) {
        if (divisor[i] > target[i])
            return false;
    }
    return true;
}

bool monomialsCoprime(const std::vector<int> &a, const std::vector<int> &b)
{
    for (std::size_t i = 0; i < a.size(); ++i) {
        if (a[i] > 0 && b[i] > 0)
            return false;
    }
    return true;
}

std::vector<int> monomialLcm(const std::vector<int> &a,
                             const std::vector<int> &b)
{
    std::vector<int> out(a.size(), 0);
    for (std::size_t i = 0; i < a.size(); ++i)
        out[i] = std::max(a[i], b[i]);
    return out;
}

std::vector<int> monomialSub(const std::vector<int> &a,
                             const std::vector<int> &b)
{
    std::vector<int> out(a.size(), 0);
    for (std::size_t i = 0; i < a.size(); ++i)
        out[i] = a[i] - b[i];
    return out;
}

std::vector<int> monomialAdd(const std::vector<int> &a,
                             const std::vector<int> &b)
{
    std::vector<int> out(a.size(), 0);
    for (std::size_t i = 0; i < a.size(); ++i)
        out[i] = a[i] + b[i];
    return out;
}

// Sparse multivariate polynomial with terms sorted in strictly descending
// monomial order (`terms[0]` is the leading term).
struct MPoly
{
    std::vector<MTerm> terms;

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
    std::vector<MTerm> merged;
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
    std::size_t i = 0, j = 0;
    while (i < a.terms.size() && j < b.terms.size()) {
        const int cmp = compareMonomial(a.terms[i].exp, b.terms[j].exp, order);
        if (cmp > 0) {
            out.terms.push_back(a.terms[i++]);
        } else if (cmp < 0) {
            out.terms.push_back(b.terms[j++]);
        } else {
            const Rational c = a.terms[i].coeff + b.terms[j].coeff;
            if (!c.isZero())
                out.terms.push_back(MTerm{c, a.terms[i].exp});
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
                   const std::vector<int> &expShift)
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
    if (lead == Rational(std::int64_t{1}))
        return;
    for (MTerm &t : p.terms)
        t.coeff = t.coeff / lead;
}

// S-polynomial S(f, g) = (lcm / LT(f)) * f - (lcm / LT(g)) * g
MPoly mpolySPoly(const MPoly &f, const MPoly &g, MonomialOrder order)
{
    const std::vector<int> lcm = monomialLcm(f.lt().exp, g.lt().exp);
    const std::vector<int> df = monomialSub(lcm, f.lt().exp);
    const std::vector<int> dg = monomialSub(lcm, g.lt().exp);
    const Rational cf = Rational(std::int64_t{1}) / f.lt().coeff;
    const Rational cg = Rational(std::int64_t{1}) / g.lt().coeff;
    return mpolySub(mpolyMulTerm(f, cf, df), mpolyMulTerm(g, cg, dg), order);
}

// Multivariate polynomial division of `f` by `G`: reduces all terms of `f`
// modulo the leading terms of `G`, returning the normal form remainder `r`.
bool mpolyReduce(const Ctx &c, const MPoly &f, const std::vector<MPoly> &G,
                 MonomialOrder order, Budget *budget, MPoly &rOut,
                 std::string &reason)
{
    MPoly p = f;
    rOut.terms.clear();
    std::size_t iter = 0;
    constexpr std::size_t kMaxDivSteps = 8192;

    while (!p.isZero()) {
        if (++iter > kMaxDivSteps) {
            reason = "multivariate division step limit exceeded";
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
                const std::vector<int> qExp = monomialSub(ltP.exp, g.lt().exp);
                p = mpolySub(p, mpolyMulTerm(g, qCoeff, qExp), order);
                divided = true;
                break;
            }
        }
        if (!divided) {
            rOut.terms.push_back(ltP);
            p.terms.erase(p.terms.begin());
        }
    }
    return true;
}

bool exprToMPolyRec(const Ctx &c, Expr e, const std::vector<Expr> &vars,
                    MonomialOrder order, MPoly &out)
{
    if (e.isNull())
        return false;
    const std::size_t k = vars.size();
    switch (c.kind(e)) {
    case NodeKind::Number: {
        out.terms.clear();
        const Rational &r = c.numberValue(e);
        if (!r.isZero())
            out.terms.push_back(MTerm{r, std::vector<int>(k, 0)});
        return true;
    }
    case NodeKind::Symbol: {
        for (std::size_t i = 0; i < k; ++i) {
            if (e == vars[i]) {
                out.terms.clear();
                std::vector<int> exp(k, 0);
                exp[i] = 1;
                out.terms.push_back(MTerm{Rational(std::int64_t{1}), std::move(exp)});
                return true;
            }
        }
        return false; // symbol not in vars
    }
    case NodeKind::Add: {
        MPoly acc;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
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
        acc.terms.push_back(MTerm{Rational(std::int64_t{1}), std::vector<int>(k, 0)});
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
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
        std::int64_t p = 0;
        if (!c.numberValue(expNode).num().fitsInt64(p) || p < 0 || p > 64)
            return false;
        MPoly bPoly;
        if (!exprToMPolyRec(c, base, vars, order, bPoly))
            return false;
        MPoly acc;
        acc.terms.push_back(MTerm{Rational(std::int64_t{1}), std::vector<int>(k, 0)});
        for (std::int64_t i = 0; i < p; ++i)
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

bool exprToMPoly(Ctx &c, Expr e, const std::vector<Expr> &vars,
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

Expr mpolyToExpr(Ctx &c, const MPoly &p, const std::vector<Expr> &vars)
{
    if (p.isZero())
        return c.zero();
    std::vector<Expr> addTerms;
    addTerms.reserve(p.terms.size());
    for (const MTerm &t : p.terms) {
        std::vector<Expr> mulFacs;
        if (t.coeff != Rational(std::int64_t{1}))
            mulFacs.push_back(c.number(t.coeff));
        for (std::size_t i = 0; i < vars.size(); ++i) {
            if (t.exp[i] == 1) {
                mulFacs.push_back(vars[i]);
            } else if (t.exp[i] > 1) {
                mulFacs.push_back(
                    c.pow(vars[i], c.number(static_cast<std::int64_t>(t.exp[i]))));
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

GroebnerResult groebnerBasis(Ctx &c, const std::vector<Expr> &polys,
                             const std::vector<Expr> &vars,
                             MonomialOrder order, Budget *budget)
{
    GroebnerResult out;
    if (vars.empty()) {
        out.reason = "empty variable list";
        return out;
    }
    for (std::size_t i = 0; i < vars.size(); ++i) {
        if (vars[i].isNull() || c.kind(vars[i]) != NodeKind::Symbol) {
            out.reason = "all Groebner variables must be Symbol nodes";
            return out;
        }
        for (std::size_t j = i + 1; j < vars.size(); ++j) {
            if (vars[i] == vars[j]) {
                out.reason = "duplicate variable in Groebner variable list";
                return out;
            }
        }
    }
    if (!checkGroebnerBudget(c, budget, out.reason))
        return out;

    std::vector<MPoly> F;
    std::vector<MPoly> G;
    for (const Expr &pe : polys) {
        if (pe.isNull()) {
            out.reason = "null polynomial in input list";
            return out;
        }
        MPoly mp;
        if (!exprToMPoly(c, pe, vars, order, mp)) {
            out.reason = "input expression is not a polynomial in Q[vars]";
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
        std::size_t i;
        std::size_t j;
        int lcmDeg;
    };
    std::vector<Pair> pairs;
    for (std::size_t i = 0; i < G.size(); ++i) {
        for (std::size_t j = i + 1; j < G.size(); ++j) {
            const int d = totalDegree(monomialLcm(G[i].lt().exp, G[j].lt().exp));
            pairs.push_back(Pair{i, j, d});
        }
    }

    constexpr std::size_t kMaxBasisSize = 96;
    while (!pairs.empty()) {
        if (!checkGroebnerBudget(c, budget, out.reason))
            return out;

        // Normal selection strategy: pick critical pair with smallest total degree of lcm(LM(g_i), LM(g_j)).
        auto bestIt = std::min_element(
            pairs.begin(), pairs.end(),
            [](const Pair &a, const Pair &b) { return a.lcmDeg < b.lcmDeg; });
        const Pair cur = *bestIt;
        pairs.erase(bestIt);

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
            out.reason = "Groebner basis size limit exceeded";
            return out;
        }
        const std::size_t newIdx = G.size();
        for (std::size_t i = 0; i < newIdx; ++i) {
            const int d =
                totalDegree(monomialLcm(G[i].lt().exp, rem.lt().exp));
            pairs.push_back(Pair{i, newIdx, d});
        }
        G.push_back(std::move(rem));
    }

    // Minimalize the Groebner basis: remove any g_i whose LM is divisible by LM(g_j) (j != i).
    std::vector<MPoly> minimal;
    for (std::size_t i = 0; i < G.size(); ++i) {
        if (G[i].isZero())
            continue;
        bool redundant = false;
        for (std::size_t j = 0; j < G.size(); ++j) {
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
    for (std::size_t i = 0; i < minimal.size(); ++i) {
        std::vector<MPoly> others;
        others.reserve(minimal.size() - 1);
        for (std::size_t j = 0; j < minimal.size(); ++j) {
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
            out.reason = "input generator failed Groebner ideal membership certificate";
            return out;
        }
    }
    for (std::size_t i = 0; i < minimal.size(); ++i) {
        for (std::size_t j = i + 1; j < minimal.size(); ++j) {
            if (monomialsCoprime(minimal[i].lt().exp, minimal[j].lt().exp))
                continue;
            const MPoly s = mpolySPoly(minimal[i], minimal[j], order);
            MPoly r;
            if (!mpolyReduce(c, s, minimal, order, budget, r, out.reason) ||
                !r.isZero()) {
                out.reason = "basis failed Buchberger S-polynomial certificate";
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

Expr polyReduceMulti(Ctx &c, Expr f, const std::vector<Expr> &G,
                     const std::vector<Expr> &vars, MonomialOrder order,
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
    std::vector<MPoly> mG;
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
    std::string reason;
    if (!mpolyReduce(c, mf, mG, order, budget, rem, reason))
        return Expr{};
    return mpolyToExpr(c, rem, vars);
}

// ============================================================================
// Multivariate Exact Division, GCD (`gcdMulti`), and Factorization (`factorMulti`)
// ============================================================================

namespace {

void collectPolyVarsRec(const Ctx &c, Expr e, std::vector<Expr> &vars)
{
    if (e.isNull())
        return;
    if (c.kind(e) == NodeKind::Symbol) {
        if (std::find(vars.begin(), vars.end(), e) == vars.end())
            vars.push_back(e);
        return;
    }
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        collectPolyVarsRec(c, c.child(e, i), vars);
}

std::vector<Expr> resolvePolyVars(const Ctx &c,
                                  const std::vector<Expr> &exprs,
                                  const std::vector<Expr> &userVars)
{
    if (!userVars.empty())
        return userVars;
    std::vector<Expr> vars;
    for (const Expr &e : exprs)
        collectPolyVarsRec(c, e, vars);
    std::sort(vars.begin(), vars.end(),
              [&](Expr a, Expr b) { return c.compare(a, b) < 0; });
    return vars;
}

MPoly mpolyConst(const Rational &r, std::size_t kVars)
{
    MPoly out;
    if (!r.isZero())
        out.terms.push_back(MTerm{r, std::vector<int>(kVars, 0)});
    return out;
}

bool mpolyIsConstant(const MPoly &p)
{
    if (p.isZero())
        return true;
    return p.terms.size() == 1 && totalDegree(p.terms[0].exp) == 0;
}

int mpolyDegInVar(const MPoly &p, std::size_t varIdx)
{
    int d = 0;
    for (const MTerm &t : p.terms) {
        if (t.exp[varIdx] > d)
            d = t.exp[varIdx];
    }
    return d;
}

std::vector<int> mpolyMinMonomial(const MPoly &p, std::size_t kVars)
{
    std::vector<int> minExp(kVars, 0);
    if (p.isZero())
        return minExp;
    minExp = p.terms[0].exp;
    for (std::size_t i = 1; i < p.terms.size(); ++i) {
        for (std::size_t j = 0; j < kVars; ++j)
            minExp[j] = std::min(minExp[j], p.terms[i].exp[j]);
    }
    return minExp;
}

MPoly mpolyShiftMonomial(const MPoly &p, const std::vector<int> &shift)
{
    MPoly out = p;
    for (MTerm &t : out.terms) {
        for (std::size_t j = 0; j < shift.size(); ++j)
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
    const std::size_t maxSteps = p.terms.size() * 8 + 64;
    std::size_t steps = 0;
    while (!p.isZero()) {
        if (++steps > maxSteps)
            return false;
        const MTerm ltP = p.lt();
        const MTerm ltB = divisor.lt();
        if (!monomialDivides(ltB.exp, ltP.exp))
            return false;
        const Rational qCoeff = ltP.coeff / ltB.coeff;
        const std::vector<int> qExp = monomialSub(ltP.exp, ltB.exp);
        qOut.terms.push_back(MTerm{qCoeff, qExp});
        p = mpolySub(p, mpolyMulTerm(divisor, qCoeff, qExp), order);
    }
    normalizeMPoly(qOut, order);
    return true;
}

MPoly mpolyDiffInVar(const MPoly &p, std::size_t varIdx, MonomialOrder order)
{
    MPoly out;
    for (const MTerm &t : p.terms) {
        const int e = t.exp[varIdx];
        if (e > 0) {
            std::vector<int> nExp = t.exp;
            nExp[varIdx] = e - 1;
            out.terms.push_back(
                MTerm{t.coeff * Rational(static_cast<std::int64_t>(e)),
                      std::move(nExp)});
        }
    }
    normalizeMPoly(out, order);
    return out;
}

std::vector<MPoly> mpolyDecomposeInVar(const MPoly &p, std::size_t varIdx,
                                       std::size_t kVars, MonomialOrder order)
{
    const int d = mpolyDegInVar(p, varIdx);
    std::vector<MPoly> coeffs(static_cast<std::size_t>(d + 1));
    for (const MTerm &t : p.terms) {
        const int e = t.exp[varIdx];
        std::vector<int> cExp = t.exp;
        cExp[varIdx] = 0;
        coeffs[static_cast<std::size_t>(e)].terms.push_back(
            MTerm{t.coeff, std::move(cExp)});
    }
    for (MPoly &cPoly : coeffs)
        normalizeMPoly(cPoly, order);
    (void)kVars;
    return coeffs;
}

MPoly mpolyComposeInVar(const std::vector<MPoly> &coeffs, std::size_t varIdx,
                        MonomialOrder order)
{
    MPoly out;
    for (std::size_t d = 0; d < coeffs.size(); ++d) {
        for (const MTerm &t : coeffs[d].terms) {
            std::vector<int> nExp = t.exp;
            nExp[varIdx] = static_cast<int>(d);
            out.terms.push_back(MTerm{t.coeff, std::move(nExp)});
        }
    }
    normalizeMPoly(out, order);
    return out;
}

UPoly mpolyToUPolyInVar(const MPoly &p, std::size_t varIdx)
{
    if (p.isZero())
        return UPoly{};
    const int d = mpolyDegInVar(p, varIdx);
    std::vector<Rational> coeffs(static_cast<std::size_t>(d + 1),
                                 Rational(std::int64_t{0}));
    for (const MTerm &t : p.terms) {
        coeffs[static_cast<std::size_t>(t.exp[varIdx])] += t.coeff;
    }
    return UPoly(std::move(coeffs));
}

MPoly upolyToMPolyInVar(const UPoly &u, std::size_t varIdx, std::size_t kVars,
                        MonomialOrder order)
{
    MPoly out;
    if (u.isZero())
        return out;
    for (int d = 0; d <= u.deg(); ++d) {
        const Rational c = u.coeff(d);
        if (!c.isZero()) {
            std::vector<int> exp(kVars, 0);
            exp[varIdx] = d;
            out.terms.push_back(MTerm{c, std::move(exp)});
        }
    }
    normalizeMPoly(out, order);
    return out;
}

MPoly mpolyGcdRec(const MPoly &a, const MPoly &b, std::size_t kVars,
                  MonomialOrder order, Budget *budget);

MPoly mpolyContentInVar(const MPoly &p, std::size_t varIdx, std::size_t kVars,
                        MonomialOrder order, Budget *budget)
{
    if (p.isZero())
        return MPoly{};
    const std::vector<MPoly> coeffs =
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
            return mpolyConst(Rational(std::int64_t{1}), kVars);
        }
    }
    mpolyMakeMonic(g);
    return g;
}

MPoly mpolyPrimitivePartInVar(const MPoly &p, std::size_t varIdx,
                              std::size_t kVars, MonomialOrder order,
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

MPoly mpolyGcdRec(const MPoly &a, const MPoly &b, std::size_t kVars,
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
        return mpolyConst(Rational(std::int64_t{1}), 0);

    // 1. Strip greatest common monomial factor x^gExp
    const std::vector<int> minA = mpolyMinMonomial(a, kVars);
    const std::vector<int> minB = mpolyMinMonomial(b, kVars);
    std::vector<int> gExp(kVars, 0);
    std::vector<int> negA(kVars, 0), negB(kVars, 0);
    for (std::size_t i = 0; i < kVars; ++i) {
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
        return finishWithMonomial(mpolyConst(Rational(std::int64_t{1}), kVars));

    MPoly qTmp;
    if (mpolyDivExact(Q, P, order, qTmp))
        return finishWithMonomial(P);
    if (mpolyDivExact(P, Q, order, qTmp))
        return finishWithMonomial(Q);

    // 2. Inspect active variables
    std::vector<std::size_t> activeVars;
    for (std::size_t i = 0; i < kVars; ++i) {
        const int da = mpolyDegInVar(P, i);
        const int db = mpolyDegInVar(Q, i);
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
        return finishWithMonomial(mpolyConst(Rational(std::int64_t{1}), kVars));

    // Base case: univariate in `activeVars[0]`
    if (activeVars.size() == 1) {
        const std::size_t v = activeVars[0];
        const UPoly uP = mpolyToUPolyInVar(P, v);
        const UPoly uQ = mpolyToUPolyInVar(Q, v);
        const UPoly uG = UPoly::gcd(uP, uQ);
        return finishWithMonomial(upolyToMPolyInVar(uG, v, kVars, order));
    }

    // 3. Pick active variable `mainVar` of smallest positive max-degree
    std::size_t mainVar = activeVars[0];
    int bestMaxDeg =
        std::max(mpolyDegInVar(P, mainVar), mpolyDegInVar(Q, mainVar));
    int bestSumDeg =
        mpolyDegInVar(P, mainVar) + mpolyDegInVar(Q, mainVar);
    for (std::size_t idx = 1; idx < activeVars.size(); ++idx) {
        const std::size_t v = activeVars[idx];
        const int mx = std::max(mpolyDegInVar(P, v), mpolyDegInVar(Q, v));
        const int sm = mpolyDegInVar(P, v) + mpolyDegInVar(Q, v);
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
    int prsIter = 0;
    while (!Q.isZero() && mpolyDegInVar(Q, mainVar) > 0 && ++prsIter <= 64) {
        if (budget && !budget->step())
            break;
        if (mpolyDivExact(P, Q, order, qTmp)) {
            P = Q;
            break;
        }
        const std::vector<MPoly> qCoeffs =
            mpolyDecomposeInVar(Q, mainVar, kVars, order);
        const int dQ = static_cast<int>(qCoeffs.size()) - 1;
        const MPoly &lcQ = qCoeffs.back();

        MPoly R = P;
        int subSteps = 0;
        while (!R.isZero() && mpolyDegInVar(R, mainVar) >= dQ &&
               ++subSteps <= 64) {
            const std::vector<MPoly> rCoeffs =
                mpolyDecomposeInVar(R, mainVar, kVars, order);
            const int dR = static_cast<int>(rCoeffs.size()) - 1;
            const MPoly &lcR = rCoeffs.back();

            // Cancel common factor between lcR and lcQ before cross-multiplying
            const MPoly gLc = mpolyGcdRec(lcR, lcQ, kVars, order, budget);
            MPoly mulR = lcQ;
            MPoly mulQ = lcR;
            if (!mpolyIsConstant(gLc)) {
                mpolyDivExact(lcQ, gLc, order, mulR);
                mpolyDivExact(lcR, gLc, order, mulQ);
            }
            std::vector<int> shiftExp(kVars, 0);
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
            P = mpolyConst(Rational(std::int64_t{1}), kVars);
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
MPoly mpolyEvalVarAtRational(const MPoly &p, std::size_t varIdx,
                             const Rational &val, MonomialOrder order)
{
    MPoly out;
    for (const MTerm &t : p.terms) {
        const int e = t.exp[varIdx];
        Rational c = t.coeff;
        if (e > 0) {
            if (val.isZero())
                continue;
            const BigInt numP =
                BigInt::powUInt(val.num(), static_cast<std::uint64_t>(e));
            const BigInt denP =
                BigInt::powUInt(val.den(), static_cast<std::uint64_t>(e));
            c = c * Rational(numP, denP);
        }
        std::vector<int> nExp = t.exp;
        nExp[varIdx] = 0;
        out.terms.push_back(MTerm{c, std::move(nExp)});
    }
    normalizeMPoly(out, order);
    return out;
}

// Shift variable `varIdx -> varIdx + shift` in `p`.
MPoly mpolyShiftVarByRational(const MPoly &p, std::size_t varIdx,
                              const Rational &shift, std::size_t kVars,
                              MonomialOrder order)
{
    if (p.isZero() || shift.isZero())
        return p;
    const std::vector<MPoly> coeffs =
        mpolyDecomposeInVar(p, varIdx, kVars, order);
    if (coeffs.size() <= 1)
        return p;

    // Horner evaluation in (x_varIdx + shift)
    MPoly xPlusShift;
    std::vector<int> e1(kVars, 0);
    e1[varIdx] = 1;
    xPlusShift.terms.push_back(MTerm{Rational(std::int64_t{1}), e1});
    xPlusShift.terms.push_back(MTerm{shift, std::vector<int>(kVars, 0)});
    normalizeMPoly(xPlusShift, order);

    MPoly acc = coeffs.back();
    for (std::size_t idx = coeffs.size() - 1; idx > 0; --idx) {
        acc = mpolyAdd(mpolyMul(acc, xPlusShift, order), coeffs[idx - 1], order);
    }
    return acc;
}

// Substitute `mainVar -> L(otherVars) * mainVar` in `p`.
MPoly mpolyScaleVarByMPoly(const MPoly &p, std::size_t mainVar, const MPoly &L,
                           std::size_t kVars, MonomialOrder order)
{
    const std::vector<MPoly> coeffs =
        mpolyDecomposeInVar(p, mainVar, kVars, order);
    if (coeffs.size() <= 1)
        return p;
    std::vector<MPoly> lPows(coeffs.size());
    lPows[0] = mpolyConst(Rational(std::int64_t{1}), kVars);
    for (std::size_t i = 1; i < coeffs.size(); ++i)
        lPows[i] = mpolyMul(lPows[i - 1], L, order);

    std::vector<MPoly> newCoeffs(coeffs.size());
    for (std::size_t i = 0; i < coeffs.size(); ++i)
        newCoeffs[i] = mpolyMul(coeffs[i], lPows[i], order);
    return mpolyComposeInVar(newCoeffs, mainVar, order);
}

// Factor a primitive, squarefree multivariate polynomial `S` (containing no
// monomial factors) into monic irreducible factors in Q[x_1, ..., x_k].
void factorPrimitiveSquarefreeMPoly(const MPoly &S, std::size_t kVars,
                                    MonomialOrder order, Budget *budget,
                                    std::vector<MPoly> &irredOut)
{
    if (S.isZero() || mpolyIsConstant(S))
        return;

    std::vector<std::size_t> activeVars;
    for (std::size_t i = 0; i < kVars; ++i) {
        if (mpolyDegInVar(S, i) > 0)
            activeVars.push_back(i);
    }
    if (activeVars.empty())
        return;

    // 1. Univariate base case
    if (activeVars.size() == 1) {
        const std::size_t v = activeVars[0];
        const UPoly uS = mpolyToUPolyInVar(S, v);
        const std::vector<UPoly> uFacs = factorOverQ(uS, budget);
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
    std::size_t mainVar = activeVars[0];
    int minDeg = mpolyDegInVar(S, mainVar);
    for (std::size_t idx = 1; idx < activeVars.size(); ++idx) {
        const int d = mpolyDegInVar(S, activeVars[idx]);
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

    std::vector<std::size_t> otherVars;
    for (std::size_t v : activeVars) {
        if (v != mainVar)
            otherVars.push_back(v);
    }

    // 3. Gauss monic transformation in `mainVar`:
    //    S(x, y) = sum_{i=0}^d A_i(y) * x^i,  L(y) = A_d(y)
    //    S_monic(X, y) = X^d + sum_{i=0}^{d-1} A_i(y) * L(y)^(d - 1 - i) * X^i
    MPoly curS = S;
    mpolyMakeMonic(curS);

    const std::vector<MPoly> sCoeffs =
        mpolyDecomposeInVar(curS, mainVar, kVars, order);
    const int dX = static_cast<int>(sCoeffs.size()) - 1;
    const MPoly L = sCoeffs.back();

    std::vector<MPoly> lPows(static_cast<std::size_t>(dX));
    lPows[0] = mpolyConst(Rational(std::int64_t{1}), kVars);
    for (int i = 1; i < dX; ++i) {
        lPows[static_cast<std::size_t>(i)] =
            mpolyMul(lPows[static_cast<std::size_t>(i - 1)], L, order);
    }

    std::vector<MPoly> monicCoeffs(static_cast<std::size_t>(dX + 1));
    monicCoeffs[static_cast<std::size_t>(dX)] =
        mpolyConst(Rational(std::int64_t{1}), kVars);
    for (int i = 0; i < dX; ++i) {
        monicCoeffs[static_cast<std::size_t>(i)] =
            mpolyMul(sCoeffs[static_cast<std::size_t>(i)],
                     lPows[static_cast<std::size_t>(dX - 1 - i)], order);
    }
    const MPoly sMonic = mpolyComposeInVar(monicCoeffs, mainVar, order);

    // 4. Find a small integer evaluation point `b` for `otherVars` such that
    //    L(b) != 0 and s0(X) = sMonic(X, b) is squarefree of degree dX.
    static const int kCandCoords[] = {0, 1, -1, 2, -2, 3, -3, 4, 5};
    std::vector<Rational> evalPt(otherVars.size(), Rational(std::int64_t{0}));
    UPoly s0;
    bool foundPt = false;
    for (int trial = 0; trial < 45 && !foundPt; ++trial) {
        int code = trial;
        for (std::size_t j = 0; j < otherVars.size(); ++j) {
            evalPt[j] = Rational(
                static_cast<std::int64_t>(kCandCoords[code % 9]));
            code /= 9;
        }
        MPoly lEval = L;
        MPoly smEval = sMonic;
        for (std::size_t j = 0; j < otherVars.size(); ++j) {
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

    std::vector<UPoly> uFactors = factorOverQ(s0, budget);
    if (uFactors.size() <= 1) {
        // Irreducible specialization => S is irreducible over Q[vars]
        irredOut.push_back(curS);
        return;
    }

    // 5. Shift `otherVars`: y_j -> u_j + evalPt[j] so the expansion point is u = 0.
    MPoly sShifted = sMonic;
    for (std::size_t j = 0; j < otherVars.size(); ++j) {
        sShifted = mpolyShiftVarByRational(sShifted, otherVars[j], evalPt[j],
                                           kVars, order);
    }

    auto otherTotalDeg = [&](const std::vector<int> &exp) -> int {
        int d = 0;
        for (std::size_t v : otherVars)
            d += exp[v];
        return d;
    };

    int maxOtherDeg = 0;
    for (const MTerm &t : sShifted.terms)
        maxOtherDeg = std::max(maxOtherDeg, otherTotalDeg(t.exp));

    // Try lifting singletons first, then pairs if needed, via Multivariate Total-Degree Hensel Lifting
    for (std::size_t subSize = 1; subSize <= uFactors.size() / 2; ++subSize) {
        if (uFactors.size() <= 1)
            break;
        std::vector<bool> mask(uFactors.size(), false);
        std::fill(mask.begin(),
                  mask.begin() + static_cast<std::ptrdiff_t>(subSize), true);

        bool factorFoundInPass = false;
        do {
            UPoly g0({Rational(std::int64_t{1})});
            UPoly h0({Rational(std::int64_t{1})});
            for (std::size_t i = 0; i < uFactors.size(); ++i) {
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
            UPoly::divMod(UPoly(Rational(std::int64_t{1})) - B * h0, g0, A,
                          remBezout);

            MPoly gLift = upolyToMPolyInVar(g0, mainVar, kVars, order);
            MPoly hLift = upolyToMPolyInVar(h0, mainVar, kVars, order);

            for (int degU = 1; degU <= maxOtherDeg; ++degU) {
                const MPoly err =
                    mpolySub(sShifted, mpolyMul(gLift, hLift, order), order);
                if (err.isZero())
                    break;

                // Group terms of `err` that have total degree `degU` in `otherVars`
                // by their `otherVars` exponent vector.
                std::map<std::vector<int>, std::vector<Rational>> buckets;
                for (const MTerm &t : err.terms) {
                    if (otherTotalDeg(t.exp) != degU)
                        continue;
                    std::vector<int> uExp = t.exp;
                    uExp[mainVar] = 0;
                    auto &vec = buckets[uExp];
                    const int xExp = t.exp[mainVar];
                    if (static_cast<int>(vec.size()) <= xExp)
                        vec.resize(static_cast<std::size_t>(xExp + 1),
                                   Rational(std::int64_t{0}));
                    vec[static_cast<std::size_t>(xExp)] += t.coeff;
                }

                for (const auto &kv : buckets) {
                    const std::vector<int> &uExp = kv.first;
                    const UPoly eAlpha(kv.second);
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
                            mpolyMulTerm(dgM, Rational(std::int64_t{1}), uExp),
                            order);
                    }
                    if (!dhAlpha.isZero()) {
                        const MPoly dhM =
                            upolyToMPolyInVar(dhAlpha, mainVar, kVars, order);
                        hLift = mpolyAdd(
                            hLift,
                            mpolyMulTerm(dhM, Rational(std::int64_t{1}), uExp),
                            order);
                    }
                }
            }

            // Unshift `otherVars`: u_j -> y_j - evalPt[j]
            MPoly gUnshifted = gLift;
            for (std::size_t j = 0; j < otherVars.size(); ++j) {
                gUnshifted = mpolyShiftVarByRational(
                    gUnshifted, otherVars[j], -evalPt[j], kVars, order);
            }
            // Undo Gauss monic scaling: X -> L(y) * x_main
            MPoly gScaled =
                mpolyScaleVarByMPoly(gUnshifted, mainVar, L, kVars, order);
            MPoly gCand =
                mpolyPrimitivePartInVar(gScaled, mainVar, kVars, order, budget);
            for (std::size_t v : otherVars) {
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

void factorArbitraryMPolyRec(const MPoly &P, int mult, std::size_t kVars,
                             MonomialOrder order, Budget *budget,
                             std::vector<std::pair<MPoly, int>> &factorsOut)
{
    if (P.isZero() || mpolyIsConstant(P))
        return;

    // 1. Strip monomial powers x_i^{m_i}
    const std::vector<int> minExp = mpolyMinMonomial(P, kVars);
    std::vector<int> negMin(kVars, 0);
    for (std::size_t i = 0; i < kVars; ++i) {
        if (minExp[i] > 0) {
            MPoly varPoly;
            std::vector<int> vExp(kVars, 0);
            vExp[i] = 1;
            varPoly.terms.push_back(
                MTerm{Rational(std::int64_t{1}), std::move(vExp)});
            factorsOut.emplace_back(std::move(varPoly), mult * minExp[i]);
        }
        negMin[i] = -minExp[i];
    }

    MPoly cur = mpolyShiftMonomial(P, negMin);
    mpolyMakeMonic(cur);
    if (mpolyIsConstant(cur))
        return;

    // 2. Make `cur` primitive in every active variable by factoring out contents
    for (std::size_t i = 0; i < kVars; ++i) {
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
    std::size_t v0 = 0;
    for (std::size_t i = 0; i < kVars; ++i) {
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
    std::vector<MPoly> irreds;
    factorPrimitiveSquarefreeMPoly(cur, kVars, order, budget, irreds);
    for (MPoly &ir : irreds) {
        mpolyMakeMonic(ir);
        if (!mpolyIsConstant(ir))
            factorsOut.emplace_back(std::move(ir), mult);
    }
}

} // namespace

Expr divExactMulti(Ctx &c, Expr f, Expr g, const std::vector<Expr> &vars,
                   Budget *budget)
{
    if (f.isNull() || g.isNull())
        return Expr{};
    const std::vector<Expr> allVars = resolvePolyVars(c, {f, g}, vars);
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

Expr gcdMulti(Ctx &c, Expr f, Expr g, const std::vector<Expr> &vars,
              Budget *budget)
{
    if (f.isNull() || g.isNull())
        return Expr{};
    const std::vector<Expr> allVars = resolvePolyVars(c, {f, g}, vars);
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

FactorMultiResult factorMulti(Ctx &c, Expr f, const std::vector<Expr> &vars,
                              Budget *budget)
{
    FactorMultiResult out;
    if (f.isNull()) {
        out.reason = "null input expression";
        return out;
    }
    const std::vector<Expr> allVars = resolvePolyVars(c, {f}, vars);
    const MonomialOrder order = MonomialOrder::Lex;
    MPoly mf;
    if (!exprToMPoly(c, f, allVars, order, mf)) {
        out.reason = "input is not a polynomial in Q[vars]";
        return out;
    }

    if (mf.isZero()) {
        out.status = FactorMultiResult::Status::ProvedSymbolic;
        out.content = Rational(std::int64_t{0});
        out.expr = c.zero();
        return out;
    }

    if (mpolyIsConstant(mf)) {
        out.status = FactorMultiResult::Status::ProvedSymbolic;
        out.content = mf.lt().coeff;
        out.expr = c.number(out.content);
        return out;
    }

    std::vector<std::pair<MPoly, int>> rawFactors;
    factorArbitraryMPolyRec(mf, 1, allVars.size(), order, budget, rawFactors);

    // Combine identical monic irreducible factors
    std::vector<FactorMultiItem> merged;
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
    MPoly prodMonic = mpolyConst(Rational(std::int64_t{1}), allVars.size());
    for (const auto &pf : rawFactors) {
        for (int m = 0; m < pf.second; ++m)
            prodMonic = mpolyMul(prodMonic, pf.first, order);
    }
    const Rational contentScalar =
        prodMonic.isZero() ? mf.lt().coeff
                           : (mf.lt().coeff / prodMonic.lt().coeff);

    std::vector<Expr> mulParts;
    if (!(contentScalar == Rational(std::int64_t{1})))
        mulParts.push_back(c.number(contentScalar));
    for (const FactorMultiItem &item : merged) {
        if (item.multiplicity == 1)
            mulParts.push_back(item.factor);
        else
            mulParts.push_back(
                c.pow(item.factor,
                      c.number(static_cast<std::int64_t>(item.multiplicity))));
    }
    const Expr reconExpr =
        mulParts.empty() ? c.number(contentScalar) : c.mul(mulParts);

    // Proof-carrying identity certificate: expand(reconExpr - f) == 0
    const Expr diffCheck = c.expand(c.add({reconExpr, c.neg(f)}));
    if (!c.isZero(diffCheck)) {
        out.reason = "multivariate factorization failed expansion certificate";
        return out;
    }

    out.status = FactorMultiResult::Status::ProvedSymbolic;
    out.content = contentScalar;
    out.factors = std::move(merged);
    out.expr = reconExpr;
    return out;
}

} // namespace numkit::cas
