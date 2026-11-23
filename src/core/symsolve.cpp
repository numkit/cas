#include <keel/core.h>
#include <keel/math.h>
#include <numkit/cas/core/symsolve.hpp>

#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/cas/poly/groebner.hpp>
#include <numkit/cas/poly/sturm.hpp>
#include <numkit/cas/poly/upoly.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

#include <algorithm>
#include <cstdlib>
#include <keel/array.h>
#include <keel/string.h>

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
    for (keel::usize i = 0; i < c.childCount(e); ++i)
        if (mentionsVar(c, c.child(e, i), var))
            return true;
    return false;
}

keel::usize countVarOccurrences(const Ctx &c, Expr e, Expr var)
{
    if (e.isNull())
        return 0;
    if (e == var)
        return 1;
    keel::usize count = 0;
    for (keel::usize i = 0; i < c.childCount(e); ++i)
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
Expr nthRootSymbolic(Ctx &c, Expr rhs, keel::i64 n)
{
    rhs = c.simplify(rhs);
    if (rhs.isNull() || n <= 1)
        return rhs;
    if (c.isZero(rhs) || rhs == c.one())
        return rhs;
    if (c.kind(rhs) != NodeKind::Pow && c.kind(rhs) != NodeKind::Number) {
        // Check if expanding & factoring in a single parameter symbol yields a
        // perfect n-th power (e.g. 1 + 4*m*(m + 1) -> (2*m + 1)^2).
        Expr singleSym;
        bool oneSym = true;
        auto findSym = [&](auto &self, Expr cur) -> void {
            if (cur.isNull() || !oneSym)
                return;
            if (c.kind(cur) == NodeKind::Symbol) {
                if (singleSym.isNull())
                    singleSym = cur;
                else if (!(singleSym == cur))
                    oneSym = false;
                return;
            }
            for (keel::usize i = 0; i < c.childCount(cur); ++i)
                self(self, c.child(cur, i));
        };
        findSym(findSym, rhs);
        if (oneSym && !singleSym.isNull()) {
            Expr fac;
            if (factorExpr(c, c.expand(rhs), singleSym, fac) && !fac.isNull())
                rhs = fac;
        }
    }
    if (c.kind(rhs) == NodeKind::Pow &&
        c.kind(c.child(rhs, 1)) == NodeKind::Number &&
        c.numberValue(c.child(rhs, 1)) == Rational(n)) {
        return c.child(rhs, 0);
    }
    if (c.kind(rhs) == NodeKind::Mul) {
        bool hasExactPowerChild = false;
        for (keel::usize i = 0; i < c.childCount(rhs); ++i) {
            const Expr ch = c.child(rhs, i);
            if (c.kind(ch) == NodeKind::Pow &&
                c.kind(c.child(ch, 1)) == NodeKind::Number &&
                c.numberValue(c.child(ch, 1)) == Rational(n)) {
                hasExactPowerChild = true;
                break;
            }
        }
        if (hasExactPowerChild) {
            keel::Array<Expr> parts;
            for (keel::usize i = 0; i < c.childCount(rhs); ++i)
                parts.push_back(nthRootSymbolic(c, c.child(rhs, i), n));
            return c.simplify(c.mul(parts));
        }
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
                const keel::i32 half = pe.second / 2;
                const keel::i32 odd = pe.second % 2;
                if (half > 0)
                    sqOut *= BigInt::powUInt(pe.first, keel::as<keel::u64>(half));
                if (odd > 0)
                    rem *= pe.first;
            }
            return c.mul({c.number(Rational(sqOut, d.den())),
                          c.pow(c.number(Rational(rem, BigInt(1))),
                                c.number(Rational(keel::i64{1}, BigInt(2))))});
        }
    }
    return c.simplify(c.pow(rhs, c.number(Rational(keel::i64{1}, BigInt(n)))));
}

void addUniqueRoot(Ctx &c, keel::Array<Expr> &roots, Expr cand)
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
        for (keel::usize i = 0; i < c.childCount(e); ++i)
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
bool extractPolyCoeffsInVar(Ctx &c, Expr poly, Expr var, keel::i32 maxDeg,
                            keel::Array<Expr> &coeffs)
{
    const Expr expd = c.expand(poly);
    if (expd.isNull())
        return false;
    if (!mentionsVar(c, expd, var)) {
        coeffs = {c.simplify(expd)};
        return true;
    }

    keel::Array<keel::Array<Expr>> buckets(keel::as<keel::usize>(maxDeg + 1));

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
            keel::i64 k = 0;
            if (rv.den() == BigInt(1) && rv.num().fitsInt64(k) && k >= 0 &&
                k <= maxDeg) {
                buckets[keel::as<keel::usize>(k)].push_back(c.one());
                return true;
            }
            return false;
        }
        if (c.kind(term) == NodeKind::Mul) {
            keel::i64 deg = 0;
            keel::Array<Expr> cofactors;
            for (keel::usize i = 0; i < c.childCount(term); ++i) {
                const Expr f = c.child(term, i);
                if (!mentionsVar(c, f, var)) {
                    cofactors.push_back(f);
                } else if (f == var) {
                    deg += 1;
                } else if (c.kind(f) == NodeKind::Pow && c.child(f, 0) == var &&
                           c.kind(c.child(f, 1)) == NodeKind::Number) {
                    const Rational &rv = c.numberValue(c.child(f, 1));
                    keel::i64 k = 0;
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
            buckets[keel::as<keel::usize>(deg)].push_back(
                cofactors.empty() ? c.one() : c.mul(cofactors));
            return true;
        }
        return false;
    };

    if (c.kind(expd) == NodeKind::Add) {
        for (keel::usize i = 0; i < c.childCount(expd); ++i)
            if (!processTerm(c.child(expd, i)))
                return false;
    } else {
        if (!processTerm(expd))
            return false;
    }

    coeffs.assign(maxDeg + 1, c.zero());
    for (keel::i32 d = 0; d <= maxDeg; ++d) {
        const auto &b = buckets[keel::as<keel::usize>(d)];
        if (!b.empty())
            coeffs[keel::as<keel::usize>(d)] = c.simplify(c.add(b));
    }
    while (coeffs.size() > 1 && isZeroAfterSimplify(c, coeffs.back()))
        coeffs.pop_back();
    return true;
}

// Peel a single-occurrence equation `lhs(var) == rhs` where `var` appears
// once in `lhs` and does not appear in `rhs`.
bool solveSingleOccurrence(Ctx &c, Expr lhs, Expr rhs, Expr var,
                           keel::Array<Expr> &out)
{
    if (lhs == var) {
        addUniqueRoot(c, out, rhs);
        return true;
    }
    switch (c.kind(lhs)) {
    case NodeKind::Add: {
        keel::usize varIdx = c.childCount(lhs);
        keel::Array<Expr> rest;
        for (keel::usize i = 0; i < c.childCount(lhs); ++i) {
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
        keel::usize varIdx = c.childCount(lhs);
        keel::Array<Expr> rest;
        for (keel::usize i = 0; i < c.childCount(lhs); ++i) {
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
                keel::i64 p = 0, q = 0;
                if (!re.num().fitsInt64(p) || !re.den().fitsInt64(q) || p == 0)
                    return false;
                if (isZeroAfterSimplify(c, rhs)) {
                    if (p < 0)
                        return true; // no solution for u^(-k) = 0
                    return solveSingleOccurrence(c, base, c.zero(), var, out);
                }
                const Rational invExp = Rational(keel::i64{1}) / re;
                if (keel::abs(p) % 2 == 0) {
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
        const keel::String &fn = c.funcName(lhs);
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
                c, arg, c.simplify(c.pow(rhs, c.number(keel::i64{2}))), var,
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
                          keel::Array<Expr> &out)
{
    // c2 * x^2 + c1 * x + c0 = 0
    const Expr four = c.number(keel::i64{4});
    const Expr two = c.number(keel::i64{2});
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

void solvePolyCoeffs(Ctx &c, keel::ArrayRef<Expr> coeffsIn,
                     keel::Array<Expr> &out)
{
    keel::Array<Expr> coeffs = keel::Array<Expr>::from(coeffsIn);
    while (coeffs.size() > 1 && isZeroAfterSimplify(c, coeffs.back()))
        coeffs.pop_back();
    if (coeffs.size() <= 1)
        return;

    // Strip common factor x^m when coeffs[0] == 0.
    keel::usize low = 0;
    while (low < coeffs.size() && isZeroAfterSimplify(c, coeffs[low]))
        ++low;
    if (low > 0) {
        addUniqueRoot(c, out, c.zero());
        coeffs = keel::Array<Expr>::from(coeffs.slice(low));
    }
    if (coeffs.size() <= 1)
        return;

    const keel::usize deg = coeffs.size() - 1;
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
    for (keel::usize i = 1; i < deg; ++i) {
        if (!isZeroAfterSimplify(c, coeffs[i])) {
            pureBinomial = false;
            break;
        }
    }
    if (pureBinomial) {
        const Expr rhs = c.simplify(c.div(c.neg(coeffs[0]), coeffs[deg]));
        const Rational invD(keel::i64{1}, BigInt(keel::as<keel::i64>(deg)));
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
        keel::Array<Expr> uRoots;
        solveQuadraticCoeffs(c, coeffs[0], coeffs[2], coeffs[4], uRoots);
        const Expr half = c.number(Rational(keel::i64{1}, BigInt(2)));
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

void collectAllSymbols(const Ctx &c, Expr e, keel::Array<Expr> &syms)
{
    if (e.isNull())
        return;
    if (c.kind(e) == NodeKind::Symbol) {
        if (std::find(syms.begin(), syms.end(), e) == syms.end())
            syms.push_back(e);
        return;
    }
    for (keel::usize i = 0; i < c.childCount(e); ++i)
        collectAllSymbols(c, c.child(e, i), syms);
}

void solveRaw(Ctx &c, Expr e, Expr var, Budget *budget,
              keel::Array<Expr> &candidates)
{
    if (e.isNull() || !checkSolveBudget(c, budget))
        return;
    if (!mentionsVar(c, e, var))
        return;

    // 1. Product of factors: solve each factor independently.
    if (c.kind(e) == NodeKind::Mul) {
        bool solvedAllFactors = true;
        for (keel::usize i = 0; i < c.childCount(e); ++i) {
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
            for (keel::usize i = 0; i < c.childCount(e); ++i) {
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
        keel::Array<Expr> numFactors;
        for (keel::usize i = 0; i < c.childCount(numExpr); ++i) {
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
    keel::Array<Expr> syms;
    collectAllSymbols(c, numExpr, syms);
    if (syms.size() == 1 && syms[0] == var) {
        UPoly upN, upD;
        if (toRational(c, numExpr, var, upN, upD) && upD.isConst() &&
            !upN.isZero()) {
            UPoly sq = upN.squarefreePart();
            sq.makeMonic();
            const keel::Array<UPoly> factors = factorOverQ(sq, budget);
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
                    const keel::Array<RootInterval> ivs = isolateRealRoots(f);
                    for (keel::usize idx = 0; idx < ivs.size(); ++idx) {
                        addUniqueRoot(c, candidates,
                                      c.rootOf(f.coeffs().clone(), keel::as<keel::i32>(idx)));
                    }
                }
            }
            return;
        }
    }

    // 5. Symbolic polynomial in `var` with symbolic parameters (degree <= 8).
    keel::Array<Expr> coeffs;
    if (extractPolyCoeffsInVar(c, numExpr, var, 8, coeffs)) {
        solvePolyCoeffs(c, keel::move(coeffs), candidates);
    }
}

} // namespace

keel::Array<Expr> solveSymbolic(Ctx &c, Expr eqn, Expr var, Budget *budget)
{
    keel::Array<Expr> raw;
    if (eqn.isNull() || var.isNull())
        return raw;
    solveRaw(c, eqn, var, budget, raw);

    // Filter out extraneous roots that hit poles of the original equation.
    keel::Array<Expr> valid;
    for (const Expr &r : raw) {
        if (!hasPoleAt(c, eqn, var, r))
            addUniqueRoot(c, valid, r);
    }
    std::sort(valid.begin(), valid.end(),
              [&c](Expr a, Expr b) { return c.compare(a, b) < 0; });
    return valid;
}

keel::Array<keel::Pair<Expr, Expr>> solveSystem2(Ctx &c, Expr eq1, Expr eq2,
                                                Expr x, Expr y, Budget *budget)
{
    keel::Array<keel::Pair<Expr, Expr>> solutions;
    if (eq1.isNull() || eq2.isNull() || x.isNull() || y.isNull())
        return solutions;

    // Extract numerators of eq1 and eq2.
    auto numeratorPart = [&](Expr e) -> Expr {
        const Expr rat = simplifyRationalExpr(c, e);
        const Expr src = rat.isNull() ? e : rat;
        if (c.kind(src) != NodeKind::Mul)
            return src;
        keel::Array<Expr> numFactors;
        for (keel::usize i = 0; i < c.childCount(src); ++i) {
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

    keel::Array<Expr> aCoeffs, bCoeffs;
    if (!extractPolyCoeffsInVar(c, F, y, 4, aCoeffs) ||
        !extractPolyCoeffsInVar(c, G, y, 4, bCoeffs)) {
        return solutions;
    }

    const keel::i32 m = keel::as<keel::i32>(aCoeffs.size()) - 1;
    const keel::i32 n = keel::as<keel::i32>(bCoeffs.size()) - 1;
    if (m < 0 || n < 0 || (m == 0 && n == 0))
        return solutions;

    keel::Array<Expr> xCandidates;
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
        const keel::usize dim = keel::as<keel::usize>(m + n);
        SymMatrix Sylv = SymMatrix::zeros(c, dim, dim);
        for (keel::i32 row = 0; row < n; ++row) {
            for (keel::i32 k = 0; k <= m; ++k) {
                Sylv.at(keel::as<keel::usize>(row),
                        keel::as<keel::usize>(row + k)) =
                    aCoeffs[keel::as<keel::usize>(m - k)];
            }
        }
        for (keel::i32 row = 0; row < m; ++row) {
            for (keel::i32 k = 0; k <= n; ++k) {
                Sylv.at(keel::as<keel::usize>(n + row),
                        keel::as<keel::usize>(row + k)) =
                    bCoeffs[keel::as<keel::usize>(n - k)];
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
        keel::Array<Expr> yCands = solveSymbolic(c, Fy, y, budget);
        const keel::Array<Expr> yCands2 = solveSymbolic(c, Gy, y, budget);
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

namespace {

Expr extractNumeratorExpr(Ctx &c, Expr e)
{
    const Expr rat = simplifyRationalExpr(c, e);
    const Expr src = rat.isNull() ? e : rat;
    if (c.kind(src) != NodeKind::Mul)
        return src;
    keel::Array<Expr> numFactors;
    for (keel::usize i = 0; i < c.childCount(src); ++i) {
        const Expr ch = c.child(src, i);
        if (c.kind(ch) == NodeKind::Pow &&
            c.kind(c.child(ch, 1)) == NodeKind::Number &&
            c.numberValue(c.child(ch, 1)).signum() < 0)
            continue;
        numFactors.push_back(ch);
    }
    return numFactors.empty() ? c.one() : c.mul(numFactors);
}

bool certifySystemTuple(Ctx &c, keel::ArrayRef<Expr> eqs,
                        keel::ArrayRef<Expr> vars,
                        keel::ArrayRef<Expr> sol)
{
    if (sol.size() != vars.size())
        return false;
    for (const Expr &eq : eqs) {
        Expr cur = eq;
        for (keel::usize i = 0; i < vars.size(); ++i) {
            if (hasPoleAt(c, cur, vars[i], sol[i]))
                return false;
            cur = c.subs(cur, vars[i], sol[i]);
        }
        if (!isZeroAfterSimplify(c, cur))
            return false;
    }
    return true;
}

void addUniqueSystemTuple(Ctx &c, keel::Array<keel::Array<Expr>> &out,
                          keel::ArrayRef<Expr> cand)
{
    for (const auto &existing : out) {
        if (existing.size() != cand.size())
            continue;
        bool same = true;
        for (keel::usize i = 0; i < cand.size(); ++i) {
            if (!isZeroAfterSimplify(c, c.add({existing[i], c.neg(cand[i])}))) {
                same = false;
                break;
            }
        }
        if (same)
            return;
    }
    out.push_back(keel::Array<Expr>::from(cand));
}

// Recursive triangular back-substitution over a Lex Groebner basis `basis`
// from `idx = k - 1` down to `0`.
void backSubstituteLexBasis(Ctx &c, keel::ArrayRef<Expr> basis,
                            keel::ArrayRef<Expr> origEqs,
                            keel::ArrayRef<Expr> vars, keel::i32 idx,
                            keel::Array<Expr> &partial, Budget *budget,
                            keel::Array<keel::Array<Expr>> &out)
{
    if (!checkSolveBudget(c, budget))
        return;
    if (idx < 0) {
        if (certifySystemTuple(c, origEqs, vars, partial))
            addUniqueSystemTuple(c, out, partial);
        return;
    }

    const keel::usize uIdx = keel::as<keel::usize>(idx);
    const Expr curVar = vars[uIdx];

    // Specialize all basis polynomials at already-bound variables vars[idx + 1 .. k - 1],
    // and collect those that depend on `curVar` and on NO earlier variables vars[0 .. idx - 1].
    keel::Array<Expr> uniPolys;
    for (const Expr &g : basis) {
        Expr spec = g;
        for (keel::usize j = uIdx + 1; j < vars.size(); ++j)
            spec = c.subs(spec, vars[j], partial[j]);
        spec = c.simplify(spec);
        if (c.isZero(spec))
            continue;
        bool hasEarlier = false;
        for (keel::i32 j = 0; j < idx; ++j) {
            if (mentionsVar(c, spec, vars[keel::as<keel::usize>(j)])) {
                hasEarlier = true;
                break;
            }
        }
        if (hasEarlier)
            continue;
        if (!mentionsVar(c, spec, curVar)) {
            // Non-zero constant residual at this specialization branch -> dead branch
            if (!isZeroAfterSimplify(c, spec))
                return;
            continue;
        }
        uniPolys.push_back(spec);
    }

    if (uniPolys.empty())
        return; // positive-dimensional component in curVar

    // Pick the lowest-cost univariate polynomial in `curVar` to solve first.
    auto bestIt = std::min_element(
        uniPolys.begin(), uniPolys.end(),
        [&](Expr a, Expr b) { return c.exprCost(a) < c.exprCost(b); });
    const keel::Array<Expr> roots = solveSymbolic(c, *bestIt, curVar, budget);
    for (const Expr &r : roots) {
        bool allVanish = true;
        for (const Expr &up : uniPolys) {
            if (!isZeroAfterSimplify(c, c.subs(up, curVar, r))) {
                allVanish = false;
                break;
            }
        }
        if (!allVanish)
            continue;
        partial[uIdx] = r;
        backSubstituteLexBasis(c, basis, origEqs, vars, idx - 1, partial,
                               budget, out);
    }
}

bool extractAffineRowRec(Ctx &c, Expr e, keel::ArrayRef<Expr> vars,
                         keel::Array<Expr> &coeffsOut, Expr &constOut)
{
    coeffsOut.assign(vars.size(), c.zero());
    constOut = c.zero();
    bool mentionsAny = false;
    for (const Expr &v : vars) {
        if (mentionsVar(c, e, v)) {
            mentionsAny = true;
            break;
        }
    }
    if (!mentionsAny) {
        constOut = e;
        return true;
    }
    for (keel::usize j = 0; j < vars.size(); ++j) {
        if (e == vars[j]) {
            coeffsOut[j] = c.one();
            return true;
        }
    }
    if (c.kind(e) == NodeKind::Add) {
        keel::Array<keel::Array<Expr>> colTerms(vars.size());
        keel::Array<Expr> constTerms;
        for (keel::usize k = 0; k < c.childCount(e); ++k) {
            keel::Array<Expr> subC;
            Expr subK;
            if (!extractAffineRowRec(c, c.child(e, k), vars, subC, subK))
                return false;
            if (!c.isZero(subK))
                constTerms.push_back(subK);
            for (keel::usize j = 0; j < vars.size(); ++j) {
                if (!c.isZero(subC[j]))
                    colTerms[j].push_back(subC[j]);
            }
        }
        constOut = constTerms.empty() ? c.zero() : c.add(constTerms);
        for (keel::usize j = 0; j < vars.size(); ++j)
            coeffsOut[j] = colTerms[j].empty() ? c.zero() : c.add(colTerms[j]);
        return true;
    }
    if (c.kind(e) == NodeKind::Mul) {
        keel::Array<Expr> freeFactors;
        Expr varFactor;
        for (keel::usize k = 0; k < c.childCount(e); ++k) {
            const Expr ch = c.child(e, k);
            bool chMentions = false;
            for (const Expr &v : vars) {
                if (mentionsVar(c, ch, v)) {
                    chMentions = true;
                    break;
                }
            }
            if (!chMentions) {
                freeFactors.push_back(ch);
            } else {
                if (!varFactor.isNull())
                    return false;
                varFactor = ch;
            }
        }
        if (varFactor.isNull()) {
            constOut = e;
            return true;
        }
        keel::Array<Expr> subC;
        Expr subK;
        if (!extractAffineRowRec(c, varFactor, vars, subC, subK))
            return false;
        const Expr scale = freeFactors.empty()
                               ? c.one()
                               : (freeFactors.size() == 1 ? freeFactors[0] : c.mul(freeFactors));
        constOut = c.isZero(subK) ? c.zero() : c.mul({scale, subK});
        for (keel::usize j = 0; j < vars.size(); ++j)
            coeffsOut[j] = c.isZero(subC[j]) ? c.zero() : c.mul({scale, subC[j]});
        return true;
    }
    return false;
}

} // namespace

keel::Array<keel::Array<Expr>> solveSystem(Ctx &c,
                                           keel::ArrayRef<Expr> eqs,
                                           keel::ArrayRef<Expr> vars,
                                           Budget *budget)
{
    keel::Array<keel::Array<Expr>> solutions;
    if (eqs.empty() || vars.empty() || !checkSolveBudget(c, budget))
        return solutions;
    for (const Expr &eq : eqs) {
        if (eq.isNull())
            return solutions;
    }
    for (keel::usize i = 0; i < vars.size(); ++i) {
        if (vars[i].isNull() || c.kind(vars[i]) != NodeKind::Symbol)
            return solutions;
        for (keel::usize j = i + 1; j < vars.size(); ++j) {
            if (vars[i] == vars[j])
                return solutions;
        }
    }

    // 1. Single-variable case
    if (vars.size() == 1) {
        const keel::Array<Expr> roots =
            solveSymbolic(c, eqs[0], vars[0], budget);
        for (const Expr &r : roots) {
            const keel::Array<Expr> tup = {r};
            if (certifySystemTuple(c, eqs, vars, tup))
                addUniqueSystemTuple(c, solutions, tup);
        }
        return solutions;
    }

    // 1b. Fast exact symbolic linear-system solver (avoids Groebner/GCD blowup
    //     on parametric linear systems with many symbolic parameters).
    if (eqs.size() == vars.size() && vars.size() >= 2 && vars.size() <= 8) {
        const keel::usize n = vars.size();
        keel::Array<keel::Array<Expr>> A(n);
        keel::Array<Expr> rhs(n);
        bool allLinear = true;
        for (keel::usize i = 0; i < n; ++i) {
            Expr b;
            if (!extractAffineRowRec(c, eqs[i], vars, A[i], b)) {
                allLinear = false;
                break;
            }
            rhs[i] = c.neg(b);
        }
        if (allLinear) {
            if (n == 2) {
                const Expr det = c.add({c.mul({A[0][0], A[1][1]}),
                                        c.neg(c.mul({A[0][1], A[1][0]}))});
                bool detZero = c.isZero(det);
                if (!detZero && c.leafCount(det) <= 256)
                    detZero = c.isZero(c.expand(det));
                if (!detZero) {
                    const Expr num0 = c.add({c.mul({rhs[0], A[1][1]}),
                                             c.neg(c.mul({A[0][1], rhs[1]}))});
                    const Expr num1 = c.add({c.mul({A[0][0], rhs[1]}),
                                             c.neg(c.mul({rhs[0], A[1][0]}))});
                    Expr x0 = c.div(num0, det);
                    Expr x1 = c.div(num1, det);
                    if (c.leafCount(x0) <= 128)
                        x0 = c.simplify(x0);
                    if (c.leafCount(x1) <= 128)
                        x1 = c.simplify(x1);
                    solutions.push_back(keel::Array<Expr>{x0, x1});
                    return solutions;
                }
            } else {
                bool singular = false;
                for (keel::usize col = 0; col < n; ++col) {
                    keel::usize pivot = n;
                    keel::usize bestCost = static_cast<keel::usize>(-1);
                    for (keel::usize r = col; r < n; ++r) {
                        if (c.isZero(A[r][col]))
                            continue;
                        if (c.leafCount(A[r][col]) <= 128 && c.isZero(c.expand(A[r][col]))) {
                            A[r][col] = c.zero();
                            continue;
                        }
                        const keel::usize cost = c.leafCount(A[r][col]);
                        if (cost < bestCost) {
                            bestCost = cost;
                            pivot = r;
                        }
                    }
                    if (pivot == n) {
                        singular = true;
                        break;
                    }
                    if (pivot != col) {
                        keel::swap(A[pivot], A[col]);
                        keel::swap(rhs[pivot], rhs[col]);
                    }
                    const Expr piv = A[col][col];
                    for (keel::usize r = col + 1; r < n; ++r) {
                        if (c.isZero(A[r][col]))
                            continue;
                        const Expr factor = c.div(A[r][col], piv);
                        A[r][col] = c.zero();
                        for (keel::usize k = col + 1; k < n; ++k) {
                            A[r][k] = c.add({A[r][k], c.neg(c.mul({factor, A[col][k]}))});
                        }
                        rhs[r] = c.add({rhs[r], c.neg(c.mul({factor, rhs[col]}))});
                    }
                }
                if (!singular) {
                    keel::Array<Expr> sol(n);
                    for (keel::i32 i = keel::as<keel::i32>(n) - 1; i >= 0; --i) {
                        const keel::usize ui = keel::as<keel::usize>(i);
                        Expr acc = rhs[ui];
                        for (keel::usize k = ui + 1; k < n; ++k) {
                            if (!c.isZero(A[ui][k]))
                                acc = c.add({acc, c.neg(c.mul({A[ui][k], sol[k]}))});
                        }
                        Expr xi = c.div(acc, A[ui][ui]);
                        if (c.leafCount(xi) <= 128)
                            xi = c.simplify(xi);
                        sol[ui] = xi;
                    }
                    solutions.push_back(keel::move(sol));
                    return solutions;
                }
            }
        }
    }

    // 2. Lexicographic Groebner basis triangular elimination over Q[vars]
    keel::Array<Expr> numEqs;
    numEqs.reserve(eqs.size());
    for (const Expr &eq : eqs)
        numEqs.push_back(extractNumeratorExpr(c, eq));

    const GroebnerResult gb =
        groebnerBasis(c, numEqs, vars, MonomialOrder::Lex, budget);
    if (gb.proved()) {
        if (gb.basis.size() == 1 && gb.basis[0] == c.one())
            return solutions; // inconsistent system (<1> unit ideal)
        keel::Array<Expr> partial(vars.size());
        backSubstituteLexBasis(c, gb.basis, eqs, vars,
                               keel::as<keel::i32>(vars.size()) - 1, partial,
                               budget, solutions);
        if (!solutions.empty())
            return solutions;
    }

    // 3. Parametric linear variable peel: if any equation is linear in some
    //    variable `vars[j]` with non-zero coefficient independent of `vars`,
    //    eliminate `vars[j]` and recurse on the remaining N - 1 variables.
    for (keel::usize eqIdx = 0; eqIdx < numEqs.size(); ++eqIdx) {
        for (keel::usize vIdx = 0; vIdx < vars.size(); ++vIdx) {
            keel::Array<Expr> lCoeffs;
            if (!extractPolyCoeffsInVar(c, numEqs[eqIdx], vars[vIdx], 1,
                                        lCoeffs) ||
                lCoeffs.size() != 2) {
                continue;
            }
            const Expr a1 = lCoeffs[1];
            bool a1DependsOnVars = false;
            for (const Expr &v : vars) {
                if (mentionsVar(c, a1, v)) {
                    a1DependsOnVars = true;
                    break;
                }
            }
            if (a1DependsOnVars || isZeroAfterSimplify(c, a1))
                continue;

            const Expr exprForVj = c.simplify(c.div(c.neg(lCoeffs[0]), a1));
            keel::Array<Expr> subEqs;
            for (keel::usize i = 0; i < eqs.size(); ++i) {
                if (i == eqIdx)
                    continue;
                subEqs.push_back(
                    c.simplify(c.subs(eqs[i], vars[vIdx], exprForVj)));
            }
            keel::Array<Expr> remVars;
            for (keel::usize i = 0; i < vars.size(); ++i) {
                if (i != vIdx)
                    remVars.push_back(vars[i]);
            }
            if (subEqs.empty())
                break;
            const auto subSols = solveSystem(c, subEqs, remVars, budget);
            for (const auto &subTup : subSols) {
                Expr valVj = exprForVj;
                for (keel::usize i = 0; i < remVars.size(); ++i)
                    valVj = c.subs(valVj, remVars[i], subTup[i]);
                valVj = c.simplify(valVj);
                keel::Array<Expr> fullTup;
                fullTup.reserve(vars.size());
                keel::usize remCursor = 0;
                for (keel::usize i = 0; i < vars.size(); ++i) {
                    if (i == vIdx)
                        fullTup.push_back(valVj);
                    else
                        fullTup.push_back(subTup[remCursor++]);
                }
                if (certifySystemTuple(c, eqs, vars, fullTup))
                    addUniqueSystemTuple(c, solutions, fullTup);
            }
            if (!solutions.empty())
                return solutions;
        }
    }

    // 4. 2-variable Sylvester resultant fallback (handles nonlinear systems with symbolic parameters)
    if (vars.size() == 2 && eqs.size() >= 2) {
        const auto pairs =
            solveSystem2(c, eqs[0], eqs[1], vars[0], vars[1], budget);
        for (const auto &pr : pairs) {
            const keel::Array<Expr> tup = {pr.first, pr.second};
            if (certifySystemTuple(c, eqs, vars, tup))
                addUniqueSystemTuple(c, solutions, tup);
        }
    }

    return solutions;
}

} // namespace numkit::cas
