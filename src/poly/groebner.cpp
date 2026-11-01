// src/poly/groebner.cpp — Buchberger's algorithm for reduced Groebner bases over Q[x_1, ..., x_k].
#include <numkit/cas/poly/groebner.hpp>

#include <numkit/cas/linalg/symmatrix.hpp>

#include <algorithm>
#include <cstdint>
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

} // namespace numkit::cas
