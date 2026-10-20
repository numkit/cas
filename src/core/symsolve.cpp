#include <numkit/cas/core/symsolve.hpp>

#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/cas/poly/sturm.hpp>
#include <numkit/cas/poly/upoly.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <vector>

namespace numkit::cas {

namespace {

bool checkSolveBudget(const Ctx &c, Budget *budget)
{
    if (!budget)
        return true;
    return budget->step() && budget->recordArenaBytes(c.nodeCount() * 32);
}

bool mentionsVar(const Ctx &c, Expr e, Expr var)
{
    if (e.isNull())
        return false;
    if (e == var)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        if (mentionsVar(c, c.child(e, i), var))
            return true;
    return false;
}

std::size_t countVarOccurrences(const Ctx &c, Expr e, Expr var)
{
    if (e.isNull())
        return 0;
    if (e == var)
        return 1;
    std::size_t count = 0;
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        count += countVarOccurrences(c, c.child(e, i), var);
    return count;
}

bool isZeroAfterSimplify(Ctx &c, Expr e)
{
    if (e.isNull())
        return false;
    if (c.isZero(e))
        return true;
    const Expr s = c.simplify(e);
    return !s.isNull() && c.isZero(s);
}

// Symbolic n-th root of `rhs` (for n >= 2):
//   - Simplifies (u^n)^(1/n) -> u
//   - Simplifies rational square roots (n == 2) by pulling out square factors
//     sqrt(a/b) = (s / b) * sqrt(rem), where a*b = s^2 * rem.
Expr nthRootSymbolic(Ctx &c, Expr rhs, std::int64_t n)
{
    rhs = c.simplify(rhs);
    if (rhs.isNull() || n <= 1)
        return rhs;
    if (c.isZero(rhs) || rhs == c.one())
        return rhs;
    if (c.kind(rhs) == NodeKind::Pow &&
        c.kind(c.child(rhs, 1)) == NodeKind::Number &&
        c.numberValue(c.child(rhs, 1)) == Rational(n)) {
        return c.child(rhs, 0);
    }
    if (n == 2 && c.kind(rhs) == NodeKind::Number &&
        c.numberValue(rhs).signum() > 0) {
        const Rational &d = c.numberValue(rhs);
        const BigInt nq = d.num() * d.den();
        BigInt exactRoot;
        if (nq.sqrtExact(exactRoot))
            return c.number(Rational(exactRoot, d.den()));
        if (nq.bitLength() <= 64 && nq > BigInt(1)) {
            BigInt sqOut(1), rem(1);
            for (const auto &pe : BigInt::factorize(nq)) {
                const int half = pe.second / 2;
                const int odd = pe.second % 2;
                if (half > 0)
                    sqOut *= BigInt::powUInt(pe.first, static_cast<std::uint64_t>(half));
                if (odd > 0)
                    rem *= pe.first;
            }
            return c.mul({c.number(Rational(sqOut, d.den())),
                          c.pow(c.number(Rational(rem, BigInt(1))),
                                c.number(Rational(std::int64_t{1}, BigInt(2))))});
        }
    }
    return c.simplify(c.pow(rhs, c.number(Rational(std::int64_t{1}, BigInt(n)))));
}

void addUniqueRoot(Ctx &c, std::vector<Expr> &roots, Expr cand)
{
    if (cand.isNull())
        return;
    const Expr s = c.simplify(cand);
    if (s.isNull())
        return;
    for (const Expr &r : roots) {
        if (r == s || isZeroAfterSimplify(c, c.add({r, c.neg(s)})))
            return;
    }
    roots.push_back(s);
}

// Check if substituting `var = root` into `expr` hits a zero denominator
// (`Pow(0, negative)` or `log(0)`).
bool hasPoleAt(Ctx &c, Expr e, Expr var, Expr root)
{
    if (e.isNull())
        return true;
    if (e == var)
        return false;
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return false;
    case NodeKind::Func: {
        if (hasPoleAt(c, c.child(e, 0), var, root))
            return true;
        if (c.funcName(e) == "log") {
            const Expr subArg = c.subs(c.child(e, 0), var, root);
            if (isZeroAfterSimplify(c, subArg))
                return true;
        }
        return false;
    }
    case NodeKind::Pow: {
        if (hasPoleAt(c, c.child(e, 0), var, root) ||
            hasPoleAt(c, c.child(e, 1), var, root))
            return true;
        const Expr ex = c.child(e, 1);
        if (c.kind(ex) == NodeKind::Number &&
            c.numberValue(ex).signum() <= 0) {
            const Expr subBase = c.subs(c.child(e, 0), var, root);
            if (isZeroAfterSimplify(c, subBase))
                return true;
        }
        return false;
    }
    case NodeKind::Add:
    case NodeKind::Mul:
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            if (hasPoleAt(c, c.child(e, i), var, root))
                return true;
        return false;
    }
    return false;
}

// Extract polynomial coefficients c_0 + c_1 * var + ... + c_d * var^d of an
// expanded expression `poly` in `var` (where coefficients may contain other
// symbols/parameters). Returns false if `poly` is not a polynomial in `var`
// of degree <= maxDeg.
bool extractPolyCoeffsInVar(Ctx &c, Expr poly, Expr var, int maxDeg,
                            std::vector<Expr> &coeffs)
{
    const Expr expd = c.expand(poly);
    if (expd.isNull())
        return false;
    if (!mentionsVar(c, expd, var)) {
        coeffs = {c.simplify(expd)};
        return true;
    }

    std::vector<std::vector<Expr>> buckets(static_cast<std::size_t>(maxDeg + 1));

    auto processTerm = [&](Expr term) -> bool {
        if (!mentionsVar(c, term, var)) {
            buckets[0].push_back(term);
            return true;
        }
        if (term == var) {
            if (maxDeg < 1)
                return false;
            buckets[1].push_back(c.one());
            return true;
        }
        if (c.kind(term) == NodeKind::Pow && c.child(term, 0) == var &&
            c.kind(c.child(term, 1)) == NodeKind::Number) {
            const Rational &rv = c.numberValue(c.child(term, 1));
            std::int64_t k = 0;
            if (rv.den() == BigInt(1) && rv.num().fitsInt64(k) && k >= 0 &&
                k <= maxDeg) {
                buckets[static_cast<std::size_t>(k)].push_back(c.one());
                return true;
            }
            return false;
        }
        if (c.kind(term) == NodeKind::Mul) {
            std::int64_t deg = 0;
            std::vector<Expr> cofactors;
            for (std::size_t i = 0; i < c.childCount(term); ++i) {
                const Expr f = c.child(term, i);
                if (!mentionsVar(c, f, var)) {
                    cofactors.push_back(f);
                } else if (f == var) {
                    deg += 1;
                } else if (c.kind(f) == NodeKind::Pow && c.child(f, 0) == var &&
                           c.kind(c.child(f, 1)) == NodeKind::Number) {
                    const Rational &rv = c.numberValue(c.child(f, 1));
                    std::int64_t k = 0;
                    if (rv.den() == BigInt(1) && rv.num().fitsInt64(k) &&
                        k >= 0) {
                        deg += k;
                    } else {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            if (deg < 0 || deg > maxDeg)
                return false;
            buckets[static_cast<std::size_t>(deg)].push_back(
                cofactors.empty() ? c.one() : c.mul(cofactors));
            return true;
        }
        return false;
    };

    if (c.kind(expd) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(expd); ++i)
            if (!processTerm(c.child(expd, i)))
                return false;
    } else {
        if (!processTerm(expd))
            return false;
    }

    coeffs.assign(static_cast<std::size_t>(maxDeg + 1), c.zero());
    for (int d = 0; d <= maxDeg; ++d) {
        const auto &b = buckets[static_cast<std::size_t>(d)];
        if (!b.empty())
            coeffs[static_cast<std::size_t>(d)] = c.simplify(c.add(b));
    }
    while (coeffs.size() > 1 && isZeroAfterSimplify(c, coeffs.back()))
        coeffs.pop_back();
    return true;
}

// Peel a single-occurrence equation `lhs(var) == rhs` where `var` appears
// once in `lhs` and does not appear in `rhs`.
bool solveSingleOccurrence(Ctx &c, Expr lhs, Expr rhs, Expr var,
                           std::vector<Expr> &out)
{
    if (lhs == var) {
        addUniqueRoot(c, out, rhs);
        return true;
    }
    switch (c.kind(lhs)) {
    case NodeKind::Add: {
        std::size_t varIdx = c.childCount(lhs);
        std::vector<Expr> rest;
        for (std::size_t i = 0; i < c.childCount(lhs); ++i) {
            const Expr ch = c.child(lhs, i);
            if (mentionsVar(c, ch, var)) {
                if (varIdx != c.childCount(lhs))
                    return false;
                varIdx = i;
            } else {
                rest.push_back(ch);
            }
        }
        if (varIdx == c.childCount(lhs))
            return false;
        const Expr newRhs =
            c.simplify(c.add({rhs, c.neg(c.add(rest))}));
        return solveSingleOccurrence(c, c.child(lhs, varIdx), newRhs, var, out);
    }
    case NodeKind::Mul: {
        std::size_t varIdx = c.childCount(lhs);
        std::vector<Expr> rest;
        for (std::size_t i = 0; i < c.childCount(lhs); ++i) {
            const Expr ch = c.child(lhs, i);
            if (mentionsVar(c, ch, var)) {
                if (varIdx != c.childCount(lhs))
                    return false;
                varIdx = i;
            } else {
                rest.push_back(ch);
            }
        }
        if (varIdx == c.childCount(lhs))
            return false;
        const Expr factor = c.simplify(c.mul(rest));
        if (isZeroAfterSimplify(c, factor))
            return false;
        const Expr newRhs = c.simplify(c.div(rhs, factor));
        return solveSingleOccurrence(c, c.child(lhs, varIdx), newRhs, var, out);
    }
    case NodeKind::Pow: {
        const Expr base = c.child(lhs, 0);
        const Expr exp = c.child(lhs, 1);
        if (mentionsVar(c, base, var) && !mentionsVar(c, exp, var)) {
            if (c.kind(exp) == NodeKind::Number) {
                const Rational &re = c.numberValue(exp);
                std::int64_t p = 0, q = 0;
                if (!re.num().fitsInt64(p) || !re.den().fitsInt64(q) || p == 0)
                    return false;
                if (isZeroAfterSimplify(c, rhs)) {
                    if (p < 0)
                        return true; // no solution for u^(-k) = 0
                    return solveSingleOccurrence(c, base, c.zero(), var, out);
                }
                const Rational invExp = Rational(std::int64_t{1}) / re;
                if (std::abs(p) % 2 == 0) {
                    if (c.kind(rhs) == NodeKind::Number &&
                        c.numberValue(rhs).signum() < 0) {
                        return true; // no real root of u^(2m) = negative
                    }
                    const Expr rootPos =
                        (q == 1 && p > 0)
                            ? nthRootSymbolic(c, rhs, p)
                            : c.simplify(c.pow(rhs, c.number(invExp)));
                    solveSingleOccurrence(c, base, rootPos, var, out);
                    solveSingleOccurrence(c, base, c.neg(rootPos), var, out);
                    return true;
                }
                Expr rootVal;
                if (c.kind(rhs) == NodeKind::Number &&
                    c.numberValue(rhs).signum() < 0) {
                    rootVal = c.neg(
                        (q == 1 && p > 0)
                            ? nthRootSymbolic(c, c.neg(rhs), p)
                            : c.simplify(c.pow(c.neg(rhs), c.number(invExp))));
                } else {
                    rootVal = (q == 1 && p > 0)
                                  ? nthRootSymbolic(c, rhs, p)
                                  : c.simplify(c.pow(rhs, c.number(invExp)));
                }
                return solveSingleOccurrence(c, base, rootVal, var, out);
            }
        }
        if (!mentionsVar(c, base, var) && mentionsVar(c, exp, var)) {
            // b^g(x) = rhs => g(x) = log(rhs) / log(b)
            if (isZeroAfterSimplify(c, rhs))
                return true;
            const Expr newRhs =
                c.simplify(c.div(c.func("log", rhs), c.func("log", base)));
            return solveSingleOccurrence(c, exp, newRhs, var, out);
        }
        return false;
    }
    case NodeKind::Func: {
        const std::string &fn = c.funcName(lhs);
        const Expr arg = c.child(lhs, 0);
        if (fn == "exp") {
            if (isZeroAfterSimplify(c, rhs) ||
                (c.kind(rhs) == NodeKind::Number &&
                 c.numberValue(rhs).signum() < 0))
                return true; // exp(u) > 0 on R
            return solveSingleOccurrence(c, arg, c.simplify(c.func("log", rhs)),
                                         var, out);
        }
        if (fn == "log") {
            return solveSingleOccurrence(c, arg, c.simplify(c.func("exp", rhs)),
                                         var, out);
        }
        if (fn == "sqrt") {
            if (c.kind(rhs) == NodeKind::Number &&
                c.numberValue(rhs).signum() < 0)
                return true;
            return solveSingleOccurrence(
                c, arg, c.simplify(c.pow(rhs, c.number(std::int64_t{2}))), var,
                out);
        }
        if (fn == "sin")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("asin", rhs)),
                                         var, out);
        if (fn == "cos")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("acos", rhs)),
                                         var, out);
        if (fn == "tan")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("atan", rhs)),
                                         var, out);
        if (fn == "asin")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("sin", rhs)),
                                         var, out);
        if (fn == "acos")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("cos", rhs)),
                                         var, out);
        if (fn == "atan")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("tan", rhs)),
                                         var, out);
        if (fn == "sinh")
            return solveSingleOccurrence(
                c, arg, c.simplify(c.func("asinh", rhs)), var, out);
        if (fn == "cosh") {
            const Expr rPos = c.simplify(c.func("acosh", rhs));
            solveSingleOccurrence(c, arg, rPos, var, out);
            solveSingleOccurrence(c, arg, c.neg(rPos), var, out);
            return true;
        }
        if (fn == "tanh")
            return solveSingleOccurrence(
                c, arg, c.simplify(c.func("atanh", rhs)), var, out);
        if (fn == "asinh")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("sinh", rhs)),
                                         var, out);
        if (fn == "acosh")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("cosh", rhs)),
                                         var, out);
        if (fn == "atanh")
            return solveSingleOccurrence(c, arg, c.simplify(c.func("tanh", rhs)),
                                         var, out);
        return false;
    }
    default:
        return false;
    }
}

void solveQuadraticCoeffs(Ctx &c, Expr c0, Expr c1, Expr c2,
                          std::vector<Expr> &out)
{
    // c2 * x^2 + c1 * x + c0 = 0
    const Expr four = c.number(std::int64_t{4});
    const Expr two = c.number(std::int64_t{2});
    const Expr disc = c.simplify(
        c.add({c.pow(c1, two), c.neg(c.mul({four, c2, c0}))}));
    if (c.kind(disc) == NodeKind::Number && c.numberValue(disc).signum() < 0)
        return; // complex conjugate pair (no real roots)
    const Expr twoA = c.mul({two, c2});
    if (isZeroAfterSimplify(c, disc)) {
        addUniqueRoot(c, out, c.div(c.neg(c1), twoA));
        return;
    }
    const Expr sqrtDisc = nthRootSymbolic(c, disc, 2);
    addUniqueRoot(c, out, c.div(c.add({c.neg(c1), c.neg(sqrtDisc)}), twoA));
    addUniqueRoot(c, out, c.div(c.add({c.neg(c1), sqrtDisc}), twoA));
}

void solvePolyCoeffs(Ctx &c, std::vector<Expr> coeffs,
                     std::vector<Expr> &out)
{
    while (coeffs.size() > 1 && isZeroAfterSimplify(c, coeffs.back()))
        coeffs.pop_back();
    if (coeffs.size() <= 1)
        return;

    // Strip common factor x^m when coeffs[0] == 0.
    std::size_t low = 0;
    while (low < coeffs.size() && isZeroAfterSimplify(c, coeffs[low]))
        ++low;
    if (low > 0) {
        addUniqueRoot(c, out, c.zero());
        coeffs.erase(coeffs.begin(),
                     coeffs.begin() + static_cast<std::ptrdiff_t>(low));
    }
    if (coeffs.size() <= 1)
        return;

    const std::size_t deg = coeffs.size() - 1;
    if (deg == 1) {
        // c1 * x + c0 = 0
        addUniqueRoot(c, out, c.div(c.neg(coeffs[0]), coeffs[1]));
        return;
    }
    if (deg == 2) {
        solveQuadraticCoeffs(c, coeffs[0], coeffs[1], coeffs[2], out);
        return;
    }

    // Check pure binomial c_d * x^d + c_0 = 0 (all intermediate coefficients 0).
    bool pureBinomial = true;
    for (std::size_t i = 1; i < deg; ++i) {
        if (!isZeroAfterSimplify(c, coeffs[i])) {
            pureBinomial = false;
            break;
        }
    }
    if (pureBinomial) {
        const Expr rhs = c.simplify(c.div(c.neg(coeffs[0]), coeffs[deg]));
        const Rational invD(std::int64_t{1}, BigInt(static_cast<std::int64_t>(deg)));
        if (deg % 2 == 0) {
            if (c.kind(rhs) == NodeKind::Number &&
                c.numberValue(rhs).signum() < 0)
                return;
            const Expr rPos = c.simplify(c.pow(rhs, c.number(invD)));
            addUniqueRoot(c, out, c.neg(rPos));
            addUniqueRoot(c, out, rPos);
        } else {
            if (c.kind(rhs) == NodeKind::Number &&
                c.numberValue(rhs).signum() < 0) {
                addUniqueRoot(
                    c, out,
                    c.neg(c.simplify(c.pow(c.neg(rhs), c.number(invD)))));
            } else {
                addUniqueRoot(c, out, c.simplify(c.pow(rhs, c.number(invD))));
            }
        }
        return;
    }

    // Biquadratic degree 4: c4 * x^4 + c2 * x^2 + c0 = 0 (c1 == 0, c3 == 0).
    if (deg == 4 && isZeroAfterSimplify(c, coeffs[1]) &&
        isZeroAfterSimplify(c, coeffs[3])) {
        std::vector<Expr> uRoots;
        solveQuadraticCoeffs(c, coeffs[0], coeffs[2], coeffs[4], uRoots);
        const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
        for (const Expr &u : uRoots) {
            if (c.kind(u) == NodeKind::Number && c.numberValue(u).signum() < 0)
                continue;
            if (isZeroAfterSimplify(c, u)) {
                addUniqueRoot(c, out, c.zero());
            } else {
                const Expr rt = c.simplify(c.pow(u, half));
                addUniqueRoot(c, out, c.neg(rt));
                addUniqueRoot(c, out, rt);
            }
        }
    }
}

void collectAllSymbols(const Ctx &c, Expr e, std::vector<Expr> &syms)
{
    if (e.isNull())
        return;
    if (c.kind(e) == NodeKind::Symbol) {
        if (std::find(syms.begin(), syms.end(), e) == syms.end())
            syms.push_back(e);
        return;
    }
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        collectAllSymbols(c, c.child(e, i), syms);
}

void solveRaw(Ctx &c, Expr e, Expr var, Budget *budget,
              std::vector<Expr> &candidates)
{
    if (e.isNull() || !checkSolveBudget(c, budget))
        return;
    if (!mentionsVar(c, e, var))
        return;

    // 1. Product of factors: solve each factor independently.
    if (c.kind(e) == NodeKind::Mul) {
        bool solvedAllFactors = true;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr ch = c.child(e, i);
            if (!mentionsVar(c, ch, var))
                continue;
            if (c.kind(ch) == NodeKind::Pow &&
                c.kind(c.child(ch, 1)) == NodeKind::Number &&
                c.numberValue(c.child(ch, 1)).signum() < 0) {
                solvedAllFactors = false;
                break;
            }
        }
        if (solvedAllFactors && c.childCount(e) >= 2) {
            for (std::size_t i = 0; i < c.childCount(e); ++i) {
                const Expr ch = c.child(e, i);
                if (mentionsVar(c, ch, var))
                    solveRaw(c, ch, var, budget, candidates);
            }
            if (!candidates.empty())
                return;
        }
    }

    // 2. Single-occurrence peel (handles both linear/power and transcendental equations).
    if (countVarOccurrences(c, e, var) == 1) {
        if (solveSingleOccurrence(c, e, c.zero(), var, candidates) &&
            !candidates.empty()) {
            return;
        }
    }

    // 3. Normalize as rational expression and extract numerator if denominator-heavy.
    const Expr rat = simplifyRationalExpr(c, e);
    Expr numExpr = rat.isNull() ? e : rat;
    if (c.kind(numExpr) == NodeKind::Mul) {
        std::vector<Expr> numFactors;
        for (std::size_t i = 0; i < c.childCount(numExpr); ++i) {
            const Expr ch = c.child(numExpr, i);
            if (c.kind(ch) == NodeKind::Pow &&
                c.kind(c.child(ch, 1)) == NodeKind::Number &&
                c.numberValue(c.child(ch, 1)).signum() < 0) {
                continue;
            }
            numFactors.push_back(ch);
        }
        numExpr = numFactors.empty() ? c.one() : c.mul(numFactors);
    }

    // 4. Univariate polynomial over Q[var]: factor via Zassenhaus `factorOverQ`.
    std::vector<Expr> syms;
    collectAllSymbols(c, numExpr, syms);
    if (syms.size() == 1 && syms[0] == var) {
        UPoly upN, upD;
        if (toRational(c, numExpr, var, upN, upD) && upD.isConst() &&
            !upN.isZero()) {
            UPoly sq = upN.squarefreePart();
            sq.makeMonic();
            const std::vector<UPoly> factors = factorOverQ(sq, budget);
            for (const UPoly &f : factors) {
                if (f.deg() == 1) {
                    addUniqueRoot(c, candidates,
                                  c.number(-f.coeff(0) / f.coeff(1)));
                } else if (f.deg() == 2) {
                    solveQuadraticCoeffs(c, c.number(f.coeff(0)),
                                         c.number(f.coeff(1)),
                                         c.number(f.coeff(2)), candidates);
                } else if (f.deg() == 4 && f.coeff(1).isZero() &&
                           f.coeff(3).isZero()) {
                    solvePolyCoeffs(c,
                                    {c.number(f.coeff(0)), c.zero(),
                                     c.number(f.coeff(2)), c.zero(),
                                     c.number(f.coeff(4))},
                                    candidates);
                } else if (f.deg() >= 3) {
                    const std::vector<RootInterval> ivs = isolateRealRoots(f);
                    for (std::size_t idx = 0; idx < ivs.size(); ++idx) {
                        addUniqueRoot(c, candidates,
                                      c.rootOf(f.coeffs(), static_cast<int>(idx)));
                    }
                }
            }
            return;
        }
    }

    // 5. Symbolic polynomial in `var` with symbolic parameters (degree <= 8).
    std::vector<Expr> coeffs;
    if (extractPolyCoeffsInVar(c, numExpr, var, 8, coeffs)) {
        solvePolyCoeffs(c, std::move(coeffs), candidates);
    }
}

} // namespace

std::vector<Expr> solveSymbolic(Ctx &c, Expr eqn, Expr var, Budget *budget)
{
    std::vector<Expr> raw;
    if (eqn.isNull() || var.isNull())
        return raw;
    solveRaw(c, eqn, var, budget, raw);

    // Filter out extraneous roots that hit poles of the original equation.
    std::vector<Expr> valid;
    for (const Expr &r : raw) {
        if (!hasPoleAt(c, eqn, var, r))
            addUniqueRoot(c, valid, r);
    }
    std::sort(valid.begin(), valid.end(),
              [&c](Expr a, Expr b) { return c.compare(a, b) < 0; });
    return valid;
}

std::vector<std::pair<Expr, Expr>> solveSystem2(Ctx &c, Expr eq1, Expr eq2,
                                                Expr x, Expr y, Budget *budget)
{
    std::vector<std::pair<Expr, Expr>> solutions;
    if (eq1.isNull() || eq2.isNull() || x.isNull() || y.isNull())
        return solutions;

    // Extract numerators of eq1 and eq2.
    auto numeratorPart = [&](Expr e) -> Expr {
        const Expr rat = simplifyRationalExpr(c, e);
        const Expr src = rat.isNull() ? e : rat;
        if (c.kind(src) != NodeKind::Mul)
            return src;
        std::vector<Expr> numFactors;
        for (std::size_t i = 0; i < c.childCount(src); ++i) {
            const Expr ch = c.child(src, i);
            if (c.kind(ch) == NodeKind::Pow &&
                c.kind(c.child(ch, 1)) == NodeKind::Number &&
                c.numberValue(c.child(ch, 1)).signum() < 0)
                continue;
            numFactors.push_back(ch);
        }
        return numFactors.empty() ? c.one() : c.mul(numFactors);
    };

    const Expr F = numeratorPart(eq1);
    const Expr G = numeratorPart(eq2);

    std::vector<Expr> aCoeffs, bCoeffs;
    if (!extractPolyCoeffsInVar(c, F, y, 4, aCoeffs) ||
        !extractPolyCoeffsInVar(c, G, y, 4, bCoeffs)) {
        return solutions;
    }

    const int m = static_cast<int>(aCoeffs.size()) - 1;
    const int n = static_cast<int>(bCoeffs.size()) - 1;
    if (m < 0 || n < 0 || (m == 0 && n == 0))
        return solutions;

    std::vector<Expr> xCandidates;
    if (m == 0) {
        // F depends only on x: solve F(x) == 0 directly.
        xCandidates = solveSymbolic(c, F, x, budget);
    } else if (n == 0) {
        // G depends only on x: solve G(x) == 0 directly.
        xCandidates = solveSymbolic(c, G, x, budget);
    } else {
        // Build the (m + n) x (m + n) Sylvester matrix Sylv_y(F, G):
        //   - First `n` rows: shifted coefficients of F (from degree m down to 0)
        //   - Next `m` rows:  shifted coefficients of G (from degree n down to 0)
        const std::size_t dim = static_cast<std::size_t>(m + n);
        SymMatrix Sylv = SymMatrix::zeros(c, dim, dim);
        for (int row = 0; row < n; ++row) {
            for (int k = 0; k <= m; ++k) {
                Sylv.at(static_cast<std::size_t>(row),
                        static_cast<std::size_t>(row + k)) =
                    aCoeffs[static_cast<std::size_t>(m - k)];
            }
        }
        for (int row = 0; row < m; ++row) {
            for (int k = 0; k <= n; ++k) {
                Sylv.at(static_cast<std::size_t>(n + row),
                        static_cast<std::size_t>(row + k)) =
                    bCoeffs[static_cast<std::size_t>(n - k)];
            }
        }
        const Expr resX = det(c, Sylv, budget);
        if (resX.isNull())
            return solutions;
        xCandidates = solveSymbolic(c, resX, x, budget);
    }

    // Back-substitute each x_i into F(x_i, y) = 0 and G(x_i, y) = 0, and
    // verify that both original equations vanish at (x_i, y_j).
    for (const Expr &xVal : xCandidates) {
        if (!checkSolveBudget(c, budget))
            break;
        const Expr Fy = c.simplify(c.subs(F, x, xVal));
        const Expr Gy = c.simplify(c.subs(G, x, xVal));
        std::vector<Expr> yCands = solveSymbolic(c, Fy, y, budget);
        const std::vector<Expr> yCands2 = solveSymbolic(c, Gy, y, budget);
        for (const Expr &yc : yCands2)
            addUniqueRoot(c, yCands, yc);

        for (const Expr &yVal : yCands) {
            if (hasPoleAt(c, eq1, x, xVal) || hasPoleAt(c, eq2, x, xVal))
                continue;
            const Expr r1 = c.subs(c.subs(eq1, x, xVal), y, yVal);
            const Expr r2 = c.subs(c.subs(eq2, x, xVal), y, yVal);
            if (isZeroAfterSimplify(c, r1) && isZeroAfterSimplify(c, r2)) {
                bool dup = false;
                for (const auto &kv : solutions) {
                    if (isZeroAfterSimplify(c, c.add({kv.first, c.neg(xVal)})) &&
                        isZeroAfterSimplify(c, c.add({kv.second, c.neg(yVal)}))) {
                        dup = true;
                        break;
                    }
                }
                if (!dup)
                    solutions.emplace_back(xVal, yVal);
            }
        }
    }

    return solutions;
}

} // namespace numkit::cas
