#include <numkit/cas/transform/ztrans.hpp>

#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/core/symsolve.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/cas/poly/upoly.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <string>
#include <vector>

namespace numkit::cas {

namespace {

bool checkZBudget(const Ctx &c, Budget *budget, std::string &reason)
{
    if (!budget)
        return true;
    if (!budget->step()) {
        reason = "step budget exhausted";
        return false;
    }
    if (!budget->recordArenaBytes(c.nodeCount() * 32)) {
        reason = "arena byte budget exhausted";
        return false;
    }
    return true;
}

bool mentionsSymbol(const Ctx &c, Expr e, Expr sym)
{
    if (e.isNull())
        return false;
    if (e == sym)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        if (mentionsSymbol(c, c.child(e, i), sym))
            return true;
    return false;
}

bool isDeltaFuncName(const std::string &fn)
{
    return fn == "kroneckerDelta" || fn == "delta";
}

// Match `arg` as `c0 + c1 * var` where `c0` and `c1` do not mention `var`.
bool matchLinearInVar(Ctx &c, Expr arg, Expr var, Expr &c0Out, Expr &c1Out)
{
    const Expr ex = c.expand(arg);
    if (!mentionsSymbol(c, ex, var)) {
        c0Out = ex;
        c1Out = c.zero();
        return true;
    }
    if (ex == var) {
        c0Out = c.zero();
        c1Out = c.one();
        return true;
    }
    auto matchLinFactor = [&](Expr term, Expr &coeffOut) -> bool {
        if (term == var) {
            coeffOut = c.one();
            return true;
        }
        if (c.kind(term) == NodeKind::Mul) {
            std::vector<Expr> others;
            bool foundVar = false;
            for (std::size_t i = 0; i < c.childCount(term); ++i) {
                const Expr ch = c.child(term, i);
                if (!foundVar && ch == var) {
                    foundVar = true;
                } else if (!mentionsSymbol(c, ch, var)) {
                    others.push_back(ch);
                } else {
                    return false;
                }
            }
            if (foundVar) {
                coeffOut = others.empty() ? c.one() : c.mul(others);
                return true;
            }
        }
        return false;
    };

    if (c.kind(ex) == NodeKind::Mul) {
        Expr cf;
        if (matchLinFactor(ex, cf)) {
            c0Out = c.zero();
            c1Out = cf;
            return true;
        }
        return false;
    }
    if (c.kind(ex) == NodeKind::Add) {
        std::vector<Expr> constTerms;
        std::vector<Expr> linCoeffs;
        for (std::size_t i = 0; i < c.childCount(ex); ++i) {
            const Expr ti = c.child(ex, i);
            if (!mentionsSymbol(c, ti, var)) {
                constTerms.push_back(ti);
            } else {
                Expr cf;
                if (!matchLinFactor(ti, cf))
                    return false;
                linCoeffs.push_back(cf);
            }
        }
        if (linCoeffs.empty())
            return false;
        c0Out = constTerms.empty() ? c.zero() : c.add(constTerms);
        c1Out = linCoeffs.size() == 1 ? linCoeffs[0] : c.add(linCoeffs);
        return true;
    }
    return false;
}

Expr rewriteHypToExpZ(Ctx &c, Expr e, Expr var)
{
    if (e.isNull() || !mentionsSymbol(c, e, var))
        return e;
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        const std::string &fn = c.funcName(e);
        const Expr u = rewriteHypToExpZ(c, c.child(e, 0), var);
        const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
        if (fn == "sinh") {
            return c.mul(
                {half, c.add({c.func("exp", u), c.neg(c.func("exp", c.neg(u)))})});
        }
        if (fn == "cosh") {
            return c.mul(
                {half, c.add({c.func("exp", u), c.func("exp", c.neg(u))})});
        }
        return c.func(fn, u);
    }
    case NodeKind::Pow:
        return c.pow(rewriteHypToExpZ(c, c.child(e, 0), var),
                     rewriteHypToExpZ(c, c.child(e, 1), var));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(rewriteHypToExpZ(c, c.child(e, i), var));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

Expr reduceTrigProductsOnceZ(Ctx &c, Expr e, Expr var, bool &changed)
{
    if (e.isNull() || !mentionsSymbol(c, e, var))
        return e;
    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));

    if (c.kind(e) == NodeKind::Pow && c.kind(c.child(e, 0)) == NodeKind::Func &&
        c.kind(c.child(e, 1)) == NodeKind::Number) {
        const std::string &fn = c.funcName(c.child(e, 0));
        const Expr u = c.child(c.child(e, 0), 0);
        std::int64_t p = 0;
        if (mentionsSymbol(c, u, var) &&
            c.numberValue(c.child(e, 1)).den() == BigInt(1) &&
            c.numberValue(c.child(e, 1)).num().fitsInt64(p) && p >= 2 &&
            p <= 6) {
            const Expr twoU = c.mul({c.number(std::int64_t{2}), u});
            Expr sq;
            if (fn == "sin")
                sq = c.mul({half, c.add({c.one(), c.neg(c.func("cos", twoU))})});
            else if (fn == "cos")
                sq = c.mul({half, c.add({c.one(), c.func("cos", twoU)})});
            else if (fn == "sinh")
                sq = c.mul({half, c.add({c.func("cosh", twoU), c.number(std::int64_t{-1})})});
            else if (fn == "cosh")
                sq = c.mul({half, c.add({c.func("cosh", twoU), c.one()})});
            if (!sq.isNull()) {
                changed = true;
                const Expr rem =
                    (p == 2) ? c.one()
                             : c.pow(c.child(e, 0), c.number(p - 2));
                return c.mul({sq, rem});
            }
        }
    }

    if (c.kind(e) == NodeKind::Mul) {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(
                reduceTrigProductsOnceZ(c, c.child(e, i), var, changed));
        for (std::size_t i = 0; i < kids.size(); ++i) {
            if (c.kind(kids[i]) != NodeKind::Func)
                continue;
            const std::string &f1 = c.funcName(kids[i]);
            if (f1 != "sin" && f1 != "cos")
                continue;
            const Expr u = c.child(kids[i], 0);
            if (!mentionsSymbol(c, u, var))
                continue;
            for (std::size_t j = i + 1; j < kids.size(); ++j) {
                if (c.kind(kids[j]) != NodeKind::Func)
                    continue;
                const std::string &f2 = c.funcName(kids[j]);
                if (f2 != "sin" && f2 != "cos")
                    continue;
                const Expr v = c.child(kids[j], 0);
                if (!mentionsSymbol(c, v, var))
                    continue;
                Expr prodSum;
                const Expr uMinusV = c.add({u, c.neg(v)});
                const Expr uPlusV = c.add({u, v});
                if (f1 == "sin" && f2 == "sin") {
                    prodSum = c.mul({half, c.add({c.func("cos", uMinusV),
                                                  c.neg(c.func("cos", uPlusV))})});
                } else if (f1 == "cos" && f2 == "cos") {
                    prodSum = c.mul({half, c.add({c.func("cos", uMinusV),
                                                  c.func("cos", uPlusV)})});
                } else if (f1 == "sin" && f2 == "cos") {
                    prodSum = c.mul({half, c.add({c.func("sin", uPlusV),
                                                  c.func("sin", uMinusV)})});
                } else {
                    prodSum = c.mul({half, c.add({c.func("sin", uPlusV),
                                                  c.neg(c.func("sin", uMinusV))})});
                }
                kids[i] = prodSum;
                kids.erase(kids.begin() + static_cast<std::ptrdiff_t>(j));
                changed = true;
                return c.mul(kids);
            }
        }
        return c.mul(kids);
    }

    if (c.kind(e) == NodeKind::Add) {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(
                reduceTrigProductsOnceZ(c, c.child(e, i), var, changed));
        return c.add(kids);
    }
    if (c.kind(e) == NodeKind::Func) {
        return c.func(c.funcName(e),
                      reduceTrigProductsOnceZ(c, c.child(e, 0), var, changed));
    }
    return e;
}

Expr normalizeForZTrans(Ctx &c, Expr e, Expr n)
{
    Expr cur = c.expand(e);
    for (int pass = 0; pass < 6; ++pass) {
        bool changed = false;
        cur = reduceTrigProductsOnceZ(c, cur, n, changed);
        cur = c.expand(cur);
        if (!changed)
            break;
    }
    return cur;
}

// Evaluate f(n) at a non-negative integer point n = k, folding kroneckerDelta(0) = 1
// and kroneckerDelta(m != 0) = 0.
Expr evalDiscreteAtInt(Ctx &c, Expr e, Expr n, std::int64_t k)
{
    const Expr sub = c.subs(e, n, c.number(k));
    auto foldDeltas = [&](auto &self, Expr node) -> Expr {
        if (node.isNull())
            return Expr();
        switch (c.kind(node)) {
        case NodeKind::Number:
        case NodeKind::Symbol:
        case NodeKind::RootOf:
            return node;
        case NodeKind::Func: {
            const Expr arg = self(self, c.child(node, 0));
            if (isDeltaFuncName(c.funcName(node))) {
                const Expr sArg = c.simplify(arg);
                if (c.isZero(sArg))
                    return c.one();
                Rational r;
                if (c.evalExact(sArg, {}, r) && !r.isZero())
                    return c.zero();
            }
            return c.func(c.funcName(node), arg);
        }
        case NodeKind::Pow: {
            const Expr b = self(self, c.child(node, 0));
            const Expr ex = self(self, c.child(node, 1));
            if (c.isZero(b) && c.isZero(ex))
                return c.one(); // 0^0 == 1 in discrete sequences r^n at n = 0
            return c.pow(b, ex);
        }
        case NodeKind::Add:
        case NodeKind::Mul: {
            std::vector<Expr> ch;
            ch.reserve(c.childCount(node));
            for (std::size_t i = 0; i < c.childCount(node); ++i)
                ch.push_back(self(self, c.child(node, i)));
            return c.kind(node) == NodeKind::Add ? c.add(ch) : c.mul(ch);
        }
        }
        return node;
    };
    return c.simplify(foldDeltas(foldDeltas, sub));
}

ZTransResult ztransTerm(Ctx &c, Expr term, Expr n, Expr z, Budget *budget)
{
    ZTransResult out;
    if (!checkZBudget(c, budget, out.reason))
        return out;

    if (!mentionsSymbol(c, term, n)) {
        // Constant c: Z{c}(z) = c * z / (z - 1).
        out.F = c.mul({term, z,
                       c.pow(c.add({z, c.number(std::int64_t{-1})}),
                             c.number(std::int64_t{-1}))});
        out.status = ZTransResult::Status::ProvedSymbolic;
        return out;
    }

    std::vector<Expr> factors;
    if (c.kind(term) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(term); ++i)
            factors.push_back(c.child(term, i));
    } else {
        factors.push_back(term);
    }

    std::vector<Expr> constFacs;
    std::vector<Expr> geomBases;
    std::vector<Expr> nonDeltaFacs;
    std::int64_t nDeg = 0;
    std::string trigFn;
    Expr trigPhase, trigFreq;
    bool hasDelta = false;
    std::int64_t deltaK = 0;

    for (const Expr &fac : factors) {
        if (!mentionsSymbol(c, fac, n)) {
            constFacs.push_back(fac);
            nonDeltaFacs.push_back(fac);
            continue;
        }
        if (fac == n) {
            nDeg += 1;
            nonDeltaFacs.push_back(fac);
            continue;
        }
        if (c.kind(fac) == NodeKind::Pow) {
            const Expr base = c.child(fac, 0);
            const Expr expNode = c.child(fac, 1);
            // n^k (k in Z_{>=1})
            if (base == n && c.kind(expNode) == NodeKind::Number) {
                const Rational &re = c.numberValue(expNode);
                std::int64_t kVal = 0;
                if (re.den() == BigInt(1) && re.num().fitsInt64(kVal) &&
                    kVal >= 1 && kVal <= 12) {
                    nDeg += kVal;
                    nonDeltaFacs.push_back(fac);
                    continue;
                }
            }
            // base^(c1*n + c0) where base does not mention n
            Expr c0, c1;
            if (!mentionsSymbol(c, base, n) &&
                matchLinearInVar(c, expNode, n, c0, c1) && !c.isZero(c1)) {
                if (!c.isZero(c0))
                    constFacs.push_back(c.pow(base, c0));
                geomBases.push_back(c.pow(base, c1));
                nonDeltaFacs.push_back(fac);
                continue;
            }
        }
        if (c.kind(fac) == NodeKind::Func) {
            const std::string &fn = c.funcName(fac);
            const Expr arg = c.child(fac, 0);
            Expr c0, c1;
            if (fn == "exp" && matchLinearInVar(c, arg, n, c0, c1) &&
                !c.isZero(c1)) {
                if (!c.isZero(c0))
                    constFacs.push_back(c.func("exp", c0));
                geomBases.push_back(c.func("exp", c1));
                nonDeltaFacs.push_back(fac);
                continue;
            }
            if ((fn == "sin" || fn == "cos" || fn == "sinh" || fn == "cosh") &&
                trigFn.empty() && matchLinearInVar(c, arg, n, c0, c1) &&
                !c.isZero(c1)) {
                trigFn = fn;
                trigPhase = c0;
                trigFreq = c1;
                nonDeltaFacs.push_back(fac);
                continue;
            }
            if (!hasDelta && isDeltaFuncName(fn) &&
                matchLinearInVar(c, arg, n, c0, c1)) {
                // Match n - k == 0 or k - n == 0 -> k = -c0 / c1.
                const Expr kExpr = c.simplify(c.neg(c.div(c0, c1)));
                Rational kRat;
                std::int64_t kVal = 0;
                if (c.evalExact(kExpr, {}, kRat) && kRat.den() == BigInt(1) &&
                    kRat.num().fitsInt64(kVal)) {
                    hasDelta = true;
                    deltaK = kVal;
                    continue;
                }
            }
        }
        out.reason = "unsupported factor in ztrans: " + c.toString(fac);
        return out;
    }

    if (hasDelta) {
        if (deltaK < 0) {
            out.F = c.zero();
            out.status = ZTransResult::Status::ProvedSymbolic;
            return out;
        }
        const Expr restExpr =
            nonDeltaFacs.empty() ? c.one() : c.mul(nonDeltaFacs);
        const Expr valAtK = evalDiscreteAtInt(c, restExpr, n, deltaK);
        out.F = c.simplify(
            c.mul({valAtK, c.pow(z, c.number(-deltaK))}));
        out.status = ZTransResult::Status::ProvedSymbolic;
        return out;
    }

    if (nDeg > 12) {
        out.reason = "polynomial degree in n exceeds ztrans limit";
        return out;
    }

    const Expr r =
        geomBases.empty() ? c.one() : c.simplify(c.mul(geomBases));
    Expr baseZ;
    if (trigFn.empty()) {
        // Z{r^n}(z) = z / (z - r).
        baseZ = c.mul({z, c.pow(c.add({z, c.neg(r)}), c.number(std::int64_t{-1}))});
    } else if (trigFn == "sin" || trigFn == "cos") {
        const Expr cosW = c.simplify(c.func("cos", trigFreq));
        const Expr sinW = c.simplify(c.func("sin", trigFreq));
        const Expr rCosW = c.mul({r, cosW});
        const Expr rSinW = c.mul({r, sinW});
        const Expr denom = c.add(
            {c.pow(z, c.number(std::int64_t{2})),
             c.neg(c.mul({c.number(std::int64_t{2}), rCosW, z})),
             c.pow(r, c.number(std::int64_t{2}))});
        const Expr invDen = c.pow(denom, c.number(std::int64_t{-1}));
        const Expr zCos = c.mul({z, c.add({z, c.neg(rCosW)}), invDen});
        const Expr zSin = c.mul({z, rSinW, invDen});
        if (c.isZero(trigPhase)) {
            baseZ = (trigFn == "cos") ? zCos : zSin;
        } else {
            const Expr cosP = c.simplify(c.func("cos", trigPhase));
            const Expr sinP = c.simplify(c.func("sin", trigPhase));
            if (trigFn == "cos") {
                baseZ = c.add(
                    {c.mul({cosP, zCos}), c.neg(c.mul({sinP, zSin}))});
            } else {
                baseZ = c.add({c.mul({sinP, zCos}), c.mul({cosP, zSin})});
            }
        }
    } else {
        const Expr coshW = c.simplify(c.func("cosh", trigFreq));
        const Expr sinhW = c.simplify(c.func("sinh", trigFreq));
        const Expr rCoshW = c.mul({r, coshW});
        const Expr rSinhW = c.mul({r, sinhW});
        const Expr denom = c.add(
            {c.pow(z, c.number(std::int64_t{2})),
             c.neg(c.mul({c.number(std::int64_t{2}), rCoshW, z})),
             c.pow(r, c.number(std::int64_t{2}))});
        const Expr invDen = c.pow(denom, c.number(std::int64_t{-1}));
        const Expr zCosh = c.mul({z, c.add({z, c.neg(rCoshW)}), invDen});
        const Expr zSinh = c.mul({z, rSinhW, invDen});
        if (c.isZero(trigPhase)) {
            baseZ = (trigFn == "cosh") ? zCosh : zSinh;
        } else {
            const Expr coshP = c.simplify(c.func("cosh", trigPhase));
            const Expr sinhP = c.simplify(c.func("sinh", trigPhase));
            if (trigFn == "cosh") {
                baseZ = c.add({c.mul({coshP, zCosh}), c.mul({sinhP, zSinh})});
            } else {
                baseZ = c.add({c.mul({sinhP, zCosh}), c.mul({coshP, zSinh})});
            }
        }
    }

    // Apply (-z * d/dz)^nDeg to baseZ.
    Expr curZ = baseZ;
    for (std::int64_t k = 0; k < nDeg; ++k) {
        if (!checkZBudget(c, budget, out.reason))
            return out;
        curZ = simplifyRationalExpr(
            c, c.neg(c.mul({z, c.diff(curZ, z)})));
    }

    const Expr cProd = constFacs.empty() ? c.one() : c.mul(constFacs);
    out.F = c.simplify(simplifyRationalExpr(c, c.mul({cProd, curZ})));
    out.status = ZTransResult::Status::ProvedSymbolic;
    return out;
}

ZTransResult ztransRec(Ctx &c, Expr f, Expr n, Expr z, Budget *budget)
{
    ZTransResult out;
    if (!checkZBudget(c, budget, out.reason))
        return out;

    const Expr norm = normalizeForZTrans(c, f, n);
    if (c.kind(norm) == NodeKind::Add) {
        std::vector<Expr> parts;
        parts.reserve(c.childCount(norm));
        for (std::size_t i = 0; i < c.childCount(norm); ++i) {
            const ZTransResult pi =
                ztransTerm(c, c.child(norm, i), n, z, budget);
            if (!pi.proved())
                return pi;
            parts.push_back(pi.F);
        }
        out.F = c.simplify(simplifyRationalExpr(c, c.add(parts)));
        out.status = ZTransResult::Status::ProvedSymbolic;
        return out;
    }
    return ztransTerm(c, norm, n, z, budget);
}

bool exprEquivalentZ(Ctx &c, Expr a, Expr b)
{
    if (a == b)
        return true;
    const Expr diff = c.add({a, c.neg(b)});
    if (c.isZero(diff))
        return true;
    const Expr rDiff = simplifyRationalExpr(c, diff);
    if (!rDiff.isNull() && c.isZero(rDiff))
        return true;
    const Expr sDiff = c.simplify(diff);
    return !sDiff.isNull() && c.isZero(sDiff);
}

// Compute binomial(n, k) = n*(n-1)*...*(n-k+1) / k! for k >= 0.
Expr binomialExpr(Ctx &c, Expr n, int k)
{
    if (k <= 0)
        return c.one();
    std::vector<Expr> numFactors;
    BigInt fact(1);
    for (int j = 0; j < k; ++j) {
        fact = fact * BigInt(j + 1);
        numFactors.push_back(
            j == 0 ? n : c.add({n, c.number(static_cast<std::int64_t>(-j))}));
    }
    numFactors.push_back(c.number(Rational(BigInt(1), fact)));
    return c.mul(numFactors);
}

// Inverse Z-transform of z / (z - r)^k for k >= 1:
//   Z^{-1}{z / (z - r)^k}(n) = binomial(n, k - 1) * r^(n - (k - 1)).
Expr invertLinearZPole(Ctx &c, Expr r, int k, Expr n)
{
    const Expr rPowN = (r == c.one()) ? c.one() : c.pow(r, n);
    if (k == 1)
        return rPowN;
    const Expr binom = binomialExpr(c, n, k - 1);
    const Expr rScale =
        (r == c.one())
            ? c.one()
            : c.pow(r, c.number(static_cast<std::int64_t>(-(k - 1))));
    return c.mul({binom, rScale, rPowN});
}

// Inverse Z-transform of z * (A*z + B) / (z^2 + b*z + d)^k (k = 1 or 2).
bool invertQuadraticZFactor(Ctx &c, const Rational &bRat, const Rational &dRat,
                            int k, const Rational &aRat, const Rational &bNumRat,
                            Expr n, Expr &out)
{
    if (k < 1 || k > 2 || dRat.isZero())
        return false;
    const Rational disc = bRat * bRat - Rational(std::int64_t{4}) * dRat;
    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));

    if (disc.signum() > 0) {
        // Real quadratic roots r1, r2 = (-b +/- sqrt(disc)) / 2.
        const Expr sqrtDisc = c.simplify(c.pow(c.number(disc), half));
        const Expr negHalfB =
            c.number(-bRat * Rational(std::int64_t{1}, BigInt(2)));
        const Expr halfSqrt = c.mul({half, sqrtDisc});
        const Expr r1 = c.add({negHalfB, halfSqrt});
        const Expr r2 = c.add({negHalfB, c.neg(halfSqrt)});
        const Expr invSqrtDisc =
            c.simplify(c.pow(c.number(disc),
                             c.number(Rational(std::int64_t{-1}, BigInt(2)))));
        if (k == 1) {
            // (A*z + B) / ((z - r1)*(z - r2)) = alpha1 / (z - r1) + alpha2 / (z - r2)
            // alpha1 = A/2 + (2*B - A*b) / (2*sqrt(disc)),
            // alpha2 = A/2 - (2*B - A*b) / (2*sqrt(disc)).
            const Expr halfA =
                c.number(aRat * Rational(std::int64_t{1}, BigInt(2)));
            const Expr diffPart = c.mul(
                {c.number((Rational(std::int64_t{2}) * bNumRat - aRat * bRat) *
                          Rational(std::int64_t{1}, BigInt(2))),
                 invSqrtDisc});
            const Expr alpha1 = c.add({halfA, diffPart});
            const Expr alpha2 = c.add({halfA, c.neg(diffPart)});
            out = c.add({c.mul({alpha1, c.pow(r1, n)}),
                         c.mul({alpha2, c.pow(r2, n)})});
            return true;
        }
        // k == 2: decompose (A*z + B) / ((z - r1)^2 * (z - r2)^2) into
        // c11/(z - r1) + c12/(z - r1)^2 + c21/(z - r2) + c22/(z - r2)^2:
        // c12 = (A*r1 + B) / disc, c22 = (A*r2 + B) / disc,
        // c11 = (A*(r1 - r2) - 2*(A*r1 + B)) / (r1 - r2)^3
        //     = -(A*(r1 + r2) + 2*B) / (disc * sqrt(disc)) = (A*b - 2*B) / (disc * sqrt(disc)),
        // c21 = -c11.
        const Expr invDisc = c.number(Rational(std::int64_t{1}) / disc);
        const Expr c12 = c.mul(
            {c.add({c.mul({c.number(aRat), r1}), c.number(bNumRat)}), invDisc});
        const Expr c22 = c.mul(
            {c.add({c.mul({c.number(aRat), r2}), c.number(bNumRat)}), invDisc});
        const Expr c11 = c.mul(
            {c.number(aRat * bRat - Rational(std::int64_t{2}) * bNumRat),
             invDisc, invSqrtDisc});
        const Expr c21 = c.neg(c11);
        out = c.add({c.mul({c11, invertLinearZPole(c, r1, 1, n)}),
                     c.mul({c12, invertLinearZPole(c, r1, 2, n)}),
                     c.mul({c21, invertLinearZPole(c, r2, 1, n)}),
                     c.mul({c22, invertLinearZPole(c, r2, 2, n)})});
        return true;
    }

    if (disc.signum() < 0 && dRat.signum() > 0) {
        // Complex-conjugate poles r * exp(+/- i*omega) with r = sqrt(d),
        // cos(omega) = -b / (2*sqrt(d)), sin(omega) = sqrt(-disc) / (2*sqrt(d)).
        const Rational negDisc = -disc;
        const Expr r = c.simplify(c.pow(c.number(dRat), half));
        const Expr invR = c.simplify(
            c.pow(c.number(dRat),
                  c.number(Rational(std::int64_t{-1}, BigInt(2)))));
        const Expr cosW = c.simplify(c.mul(
            {c.number(-bRat * Rational(std::int64_t{1}, BigInt(2))), invR}));
        const Expr omega = c.simplify(c.func("acos", cosW));
        const Expr rPowN = (r == c.one()) ? c.one() : c.pow(r, n);
        const Expr cosWn = c.func("cos", c.mul({omega, n}));
        const Expr sinWn = c.func("sin", c.mul({omega, n}));
        const Expr invSqrtNegDisc = c.simplify(
            c.pow(c.number(negDisc),
                  c.number(Rational(std::int64_t{-1}, BigInt(2)))));
        if (k == 1) {
            // z*(A*z + B) / (z^2 + b*z + d)
            //   = A * z*(z + b/2)/Q + ((2*B - A*b)/sqrt(-disc)) * z*(sqrt(-disc)/2)/Q
            const Expr sinCoeff = c.mul(
                {c.number(Rational(std::int64_t{2}) * bNumRat - aRat * bRat),
                 invSqrtNegDisc});
            out = c.add({c.mul({c.number(aRat), rPowN, cosWn}),
                         c.mul({sinCoeff, rPowN, sinWn})});
            return true;
        }
    }
    return false;
}

bool iztransFromRationalQ(Ctx &c, Expr F, Expr z, Expr n, Budget *budget,
                          Expr &out)
{
    UPoly N, D;
    if (!toRational(c, F, z, N, D) || D.isZero())
        return false;
    if (N.isZero()) {
        out = c.zero();
        return true;
    }

    const UPoly gnd = UPoly::gcd(N, D);
    if (gnd.deg() >= 1) {
        UPoly qN, rN, qD, rD;
        UPoly::divMod(N, gnd, qN, rN);
        UPoly::divMod(D, gnd, qD, rD);
        N = qN;
        D = qD;
    }

    // Factor out z^p from D(z): D(z) = z^p * dTilde(z) with dTilde(0) != 0.
    int pZero = 0;
    while (pZero <= D.deg() && D.coeff(static_cast<std::size_t>(pZero)).isZero())
        ++pZero;
    std::vector<Rational> dTildeCoeffs;
    for (int i = pZero; i <= D.deg(); ++i)
        dTildeCoeffs.push_back(D.coeff(static_cast<std::size_t>(i)));
    UPoly dTilde(dTildeCoeffs);

    // Require causal sequence: deg(N) <= deg(D).
    if (N.deg() > D.deg())
        return false;

    // Decompose F(z)/z = N(z) / (z^(pZero+1) * dTilde(z)):
    //   1. If dTilde is constant, F(z) = sum_{k=0}^pZero c_k * z^(-k).
    const UPoly zPow = UPoly::monomial(
        Rational(std::int64_t{1}), static_cast<std::uint64_t>(pZero + 1));
    std::vector<Expr> seqTerms;

    UPoly mPoly;
    if (dTilde.deg() == 0) {
        const Rational invC = Rational(std::int64_t{1}) / dTilde.coeff(0);
        for (int i = 0; i <= N.deg(); ++i) {
            const Rational ci = N.coeff(static_cast<std::size_t>(i)) * invC;
            if (ci.isZero())
                continue;
            const int kShift = pZero - i;
            if (kShift < 0)
                return false;
            const Expr deltaArg =
                (kShift == 0)
                    ? n
                    : c.add({n, c.number(static_cast<std::int64_t>(-kShift))});
            seqTerms.push_back(
                c.mul({c.number(ci), c.func("kroneckerDelta", deltaArg)}));
        }
        out = seqTerms.empty() ? c.zero() : c.simplify(c.add(seqTerms));
        return true;
    }

    // Normalize dTilde to be monic.
    const Rational dLc = dTilde.lc();
    dTilde.makeMonic();
    N = N * UPoly(Rational(std::int64_t{1}) / dLc);

    // N(z) / (z^(pZero+1) * dTilde(z)) = p0(z) / z^(pZero+1) + mPoly(z) / dTilde(z)
    // where p0(z) = (N * invMod(dTilde, z^(pZero+1))) mod z^(pZero+1).
    const UPoly invDTilde = UPoly::invMod(dTilde % zPow, zPow);
    const UPoly p0 = (N * invDTilde) % zPow;
    for (int i = 0; i <= p0.deg(); ++i) {
        const Rational ci = p0.coeff(static_cast<std::size_t>(i));
        if (ci.isZero())
            continue;
        const int kShift = pZero - i;
        if (kShift < 0)
            return false;
        const Expr deltaArg =
            (kShift == 0)
                ? n
                : c.add({n, c.number(static_cast<std::int64_t>(-kShift))});
        seqTerms.push_back(
            c.mul({c.number(ci), c.func("kroneckerDelta", deltaArg)}));
    }

    const UPoly remNum = N - p0 * dTilde;
    UPoly rZero;
    UPoly::divMod(remNum, zPow, mPoly, rZero);
    if (!rZero.isZero() || mPoly.deg() >= dTilde.deg())
        return false;

    if (!mPoly.isZero()) {
        std::vector<UPoly> irreds = factorOverQ(dTilde, budget);
        if (budget && !budget->ok())
            return false;
        struct IrredFactor
        {
            UPoly q;
            int mult = 0;
            UPoly qPow;
        };
        std::vector<IrredFactor> fs;
        for (const UPoly &ir : irreds) {
            if (ir.deg() != 1 && ir.deg() != 2)
                return false;
            bool found = false;
            for (auto &f : fs) {
                if (f.q == ir) {
                    f.mult += 1;
                    f.qPow = f.qPow * ir;
                    found = true;
                    break;
                }
            }
            if (!found)
                fs.push_back(IrredFactor{ir, 1, ir});
        }

        for (std::size_t j = 0; j < fs.size(); ++j) {
            UPoly mj(Rational(std::int64_t{1}));
            for (std::size_t i = 0; i < fs.size(); ++i) {
                if (i != j)
                    mj = mj * fs[i].qPow;
            }
            const UPoly invMj = UPoly::invMod(mj % fs[j].qPow, fs[j].qPow);
            UPoly cur = (mPoly * invMj) % fs[j].qPow;

            for (int k = fs[j].mult; k >= 1 && !cur.isZero(); --k) {
                UPoly quot, rem;
                UPoly::divMod(cur, fs[j].q, quot, rem);
                cur = quot;
                if (rem.isZero())
                    continue;
                if (fs[j].q.deg() == 1) {
                    const Rational rRat = -fs[j].q.coeff(0);
                    const Rational cRat = rem.coeff(0);
                    seqTerms.push_back(c.mul(
                        {c.number(cRat),
                         invertLinearZPole(c, c.number(rRat), k, n)}));
                } else {
                    Expr qTerm;
                    if (!invertQuadraticZFactor(c, fs[j].q.coeff(1),
                                                fs[j].q.coeff(0), k,
                                                rem.coeff(1), rem.coeff(0), n,
                                                qTerm)) {
                        return false;
                    }
                    seqTerms.push_back(qTerm);
                }
            }
        }
    }

    out = seqTerms.empty() ? c.zero() : c.simplify(c.add(seqTerms));
    return true;
}

// Parametric fallback for symbolic poles F(z) = z * P(z) / (z - a)^k.
bool iztransParametric(Ctx &c, Expr F, Expr z, Expr n, Expr &out)
{
    const Expr fOverZ = simplifyRationalExpr(c, c.div(F, z));
    std::vector<Expr> factors;
    if (c.kind(fOverZ) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(fOverZ); ++i)
            factors.push_back(c.child(fOverZ, i));
    } else {
        factors.push_back(fOverZ);
    }

    Expr linBase;
    int poleK = 0;
    std::vector<Expr> numFacs;
    for (const Expr &fac : factors) {
        if (poleK == 0 && c.kind(fac) == NodeKind::Pow &&
            c.kind(c.child(fac, 1)) == NodeKind::Number) {
            const Rational &re = c.numberValue(c.child(fac, 1));
            std::int64_t kVal = 0;
            Expr c0, c1;
            if (re.den() == BigInt(1) && re.num().fitsInt64(kVal) &&
                kVal <= -1 && kVal >= -6 &&
                matchLinearInVar(c, c.child(fac, 0), z, c0, c1) &&
                !c.isZero(c1)) {
                linBase = c.child(fac, 0);
                poleK = static_cast<int>(-kVal);
                continue;
            }
        }
        numFacs.push_back(fac);
    }
    if (poleK < 1)
        return false;

    Expr c0, c1;
    matchLinearInVar(c, linBase, z, c0, c1);
    const Expr r = c.simplify(c.neg(c.div(c0, c1)));
    if (c.isZero(r))
        return false;
    const Expr numExpr = numFacs.empty() ? c.one() : c.mul(numFacs);
    if (!mentionsSymbol(c, numExpr, z)) {
        const Expr scale =
            c.mul({numExpr, c.pow(c1, c.number(static_cast<std::int64_t>(-poleK)))});
        out = c.simplify(c.mul({scale, invertLinearZPole(c, r, poleK, n)}));
        return true;
    }
    return false;
}

} // namespace

ZTransResult ztrans(Ctx &c, Expr f, Expr n, Expr z, Budget *budget)
{
    ZTransResult out;
    if (f.isNull() || n.isNull() || z.isNull() || c.kind(n) != NodeKind::Symbol) {
        out.reason = "invalid input to ztrans";
        return out;
    }
    return ztransRec(c, f, n, z, budget);
}

ZTransResult iztrans(Ctx &c, Expr F, Expr z, Expr n, Budget *budget)
{
    ZTransResult out;
    if (F.isNull() || z.isNull() || n.isNull() || c.kind(z) != NodeKind::Symbol) {
        out.reason = "invalid input to iztrans";
        return out;
    }
    if (!checkZBudget(c, budget, out.reason))
        return out;

    const Expr fNorm = simplifyRationalExpr(c, F);
    Expr cand;
    bool ok = iztransFromRationalQ(c, fNorm, z, n, budget, cand);
    if (!ok && (!budget || budget->ok()))
        ok = iztransParametric(c, fNorm, z, n, cand);
    if (!ok && c.kind(F) == NodeKind::Add) {
        std::vector<Expr> parts;
        bool allOk = true;
        for (std::size_t i = 0; i < c.childCount(F); ++i) {
            const ZTransResult sub = iztrans(c, c.child(F, i), z, n, budget);
            if (!sub.proved()) {
                allOk = false;
                break;
            }
            parts.push_back(sub.F);
        }
        if (allOk) {
            cand = c.simplify(c.add(parts));
            ok = true;
        }
    }

    if (!ok || cand.isNull()) {
        if (out.reason.empty())
            out.reason = "unable to invert Z-transform";
        return out;
    }

    // Round-trip verification certificate: Z{cand}(z) == F(z).
    const ZTransResult check = ztrans(c, cand, n, z, budget);
    if (!check.proved() || !exprEquivalentZ(c, check.F, F)) {
        out.reason = "inverse Z-transform round-trip certificate failed";
        return out;
    }
    out.F = cand;
    out.status = ZTransResult::Status::ProvedSymbolic;
    return out;
}

namespace {

// Expand shifts inside a sequence expression y(n + k) so recurrence residuals
// cancel canonically:
//   - r^(n + k) -> r^k * r^n
//   - sin(w*(n + k)) -> cos(w*k)*sin(w*n) + sin(w*k)*cos(w*n)
//   - cos(w*(n + k)) -> cos(w*k)*cos(w*n) - sin(w*k)*sin(w*n)
Expr expandSequenceShifts(Ctx &c, Expr e, Expr n)
{
    if (e.isNull() || !mentionsSymbol(c, e, n))
        return e;
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Pow: {
        const Expr b = expandSequenceShifts(c, c.child(e, 0), n);
        const Expr ex = expandSequenceShifts(c, c.child(e, 1), n);
        Expr c0, c1;
        if (!mentionsSymbol(c, b, n) && matchLinearInVar(c, ex, n, c0, c1) &&
            !c.isZero(c1) && !c.isZero(c0)) {
            return c.mul({c.simplify(c.pow(b, c0)),
                          c.pow(b, c.mul({c1, n}))});
        }
        return c.pow(b, ex);
    }
    case NodeKind::Func: {
        const std::string &fn = c.funcName(e);
        const Expr arg = expandSequenceShifts(c, c.child(e, 0), n);
        Expr c0, c1;
        if ((fn == "sin" || fn == "cos") &&
            matchLinearInVar(c, arg, n, c0, c1) && !c.isZero(c1) &&
            !c.isZero(c0)) {
            const Expr wn = c.mul({c1, n});
            const Expr cosC0 = c.simplify(c.func("cos", c0));
            const Expr sinC0 = c.simplify(c.func("sin", c0));
            if (fn == "sin") {
                return c.add({c.mul({cosC0, c.func("sin", wn)}),
                              c.mul({sinC0, c.func("cos", wn)})});
            }
            return c.add({c.mul({cosC0, c.func("cos", wn)}),
                          c.neg(c.mul({sinC0, c.func("sin", wn)}))});
        }
        if (isDeltaFuncName(fn))
            return c.zero(); // for asymptotic recurrence check n >= K
        return c.func(fn, arg);
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            ch.push_back(expandSequenceShifts(c, c.child(e, i), n));
        return c.kind(e) == NodeKind::Add ? c.add(ch) : c.mul(ch);
    }
    }
    return e;
}

bool certifyRecurrence(Ctx &c, const std::vector<Expr> &coeffs, Expr rhs,
                       Expr y, Expr n)
{
    std::vector<Expr> lhsTerms;
    for (std::size_t k = 0; k < coeffs.size(); ++k) {
        if (c.isZero(coeffs[k]))
            continue;
        const Expr nPlusK =
            (k == 0) ? n : c.add({n, c.number(static_cast<std::int64_t>(k))});
        const Expr yk = c.subs(y, n, nPlusK);
        lhsTerms.push_back(c.mul({coeffs[k], yk}));
    }
    const Expr rawRes =
        c.add({lhsTerms.empty() ? c.zero() : c.add(lhsTerms), c.neg(rhs)});
    const Expr expRes = c.expand(expandSequenceShifts(c, rawRes, n));
    if (c.isZero(expRes))
        return true;
    const Expr simpRes = c.simplify(expRes);
    if (!simpRes.isNull() && c.isZero(simpRes))
        return true;
    const Expr ratRes = simplifyRationalExpr(c, simpRes);
    return !ratRes.isNull() && c.isZero(ratRes);
}

} // namespace

RsolveResult rsolveIVP(Ctx &c, const std::vector<Expr> &coeffs, Expr rhs,
                       Expr n, const std::vector<Expr> &initVals,
                       Budget *budget)
{
    RsolveResult out;
    if (coeffs.size() < 2 || rhs.isNull() || n.isNull() ||
        c.kind(n) != NodeKind::Symbol) {
        out.reason = "invalid recurrence specification";
        return out;
    }
    std::size_t orderK = coeffs.size() - 1;
    while (orderK > 0 && c.isZero(coeffs[orderK]))
        --orderK;
    if (orderK == 0) {
        out.reason = "leading recurrence coefficient is zero";
        return out;
    }
    if (initVals.size() < orderK) {
        out.reason = "insufficient initial values for recurrence order";
        return out;
    }
    if (!checkZBudget(c, budget, out.reason))
        return out;

    const Expr z = c.symbol("_z_rsolve");
    // Build characteristic polynomial P(z) = sum_{k=0}^K a_k * z^k
    // and initial-condition numerator I(z) = sum_{k=1}^K a_k * sum_{j=0}^{k-1} y(j) * z^(k - j).
    std::vector<Expr> pTerms;
    std::vector<Expr> initTerms;
    for (std::size_t k = 0; k <= orderK; ++k) {
        if (c.isZero(coeffs[k]))
            continue;
        pTerms.push_back(
            k == 0 ? coeffs[0]
                   : c.mul({coeffs[k],
                            c.pow(z, c.number(static_cast<std::int64_t>(k)))}));
        for (std::size_t j = 0; j < k; ++j) {
            if (c.isZero(initVals[j]))
                continue;
            initTerms.push_back(c.mul(
                {coeffs[k], initVals[j],
                 c.pow(z, c.number(static_cast<std::int64_t>(k - j)))}));
        }
    }
    const Expr pZ = pTerms.empty() ? c.zero() : c.add(pTerms);
    const Expr initZ = initTerms.empty() ? c.zero() : c.add(initTerms);

    Expr rhsZ = c.zero();
    if (!c.isZero(rhs)) {
        const ZTransResult zr = ztrans(c, rhs, n, z, budget);
        if (!zr.proved()) {
            out.reason = "unable to Z-transform recurrence right-hand side: " +
                         zr.reason;
            return out;
        }
        rhsZ = zr.F;
    }

    const Expr yZ = simplifyRationalExpr(c, c.div(c.add({rhsZ, initZ}), pZ));
    const ZTransResult inv = iztrans(c, yZ, z, n, budget);
    if (!inv.proved()) {
        out.reason = "unable to invert Z-transform of recurrence solution: " +
                     inv.reason;
        return out;
    }

    std::vector<Expr> trimmedCoeffs(coeffs.begin(),
                                    coeffs.begin() +
                                        static_cast<std::ptrdiff_t>(orderK + 1));
    if (!certifyRecurrence(c, trimmedCoeffs, rhs, inv.F, n)) {
        out.reason = "recurrence solution failed residual certificate";
        return out;
    }
    for (std::size_t j = 0; j < orderK; ++j) {
        const Expr yAtJ =
            evalDiscreteAtInt(c, inv.F, n, static_cast<std::int64_t>(j));
        const Expr err = c.simplify(c.add({yAtJ, c.neg(initVals[j])}));
        if (err.isNull() || !c.isZero(err)) {
            out.reason = "recurrence solution failed initial value certificate";
            return out;
        }
    }

    out.y = inv.F;
    out.status = RsolveResult::Status::ProvedSymbolic;
    return out;
}

RsolveResult rsolve(Ctx &c, const std::vector<Expr> &coeffs, Expr rhs, Expr n,
                    Budget *budget)
{
    RsolveResult out;
    if (coeffs.size() < 2 || rhs.isNull() || n.isNull() ||
        c.kind(n) != NodeKind::Symbol) {
        out.reason = "invalid recurrence specification";
        return out;
    }
    std::size_t orderK = coeffs.size() - 1;
    while (orderK > 0 && c.isZero(coeffs[orderK]))
        --orderK;
    if (orderK == 0) {
        out.reason = "leading recurrence coefficient is zero";
        return out;
    }
    if (!checkZBudget(c, budget, out.reason))
        return out;

    const Expr z = c.symbol("_z_char");
    std::vector<Expr> pTerms;
    for (std::size_t k = 0; k <= orderK; ++k) {
        if (!c.isZero(coeffs[k])) {
            pTerms.push_back(
                k == 0
                    ? coeffs[0]
                    : c.mul({coeffs[k],
                             c.pow(z, c.number(static_cast<std::int64_t>(k)))}));
        }
    }
    const Expr pZ = c.add(pTerms);

    // Build K homogeneous basis modes from the roots/factors of P(z).
    std::vector<Expr> basis;
    UPoly pNum, pDen;
    if (toRational(c, pZ, z, pNum, pDen) && pDen.isConst() && !pNum.isZero()) {
        int zeroMult = 0;
        while (zeroMult <= pNum.deg() &&
               pNum.coeff(static_cast<std::size_t>(zeroMult)).isZero()) {
            const Expr deltaArg =
                (zeroMult == 0)
                    ? n
                    : c.add({n, c.number(static_cast<std::int64_t>(-zeroMult))});
            basis.push_back(c.func("kroneckerDelta", deltaArg));
            ++zeroMult;
        }
        std::vector<Rational> nzCoeffs;
        for (int i = zeroMult; i <= pNum.deg(); ++i)
            nzCoeffs.push_back(pNum.coeff(static_cast<std::size_t>(i)));
        UPoly nzPoly(nzCoeffs);
        nzPoly.makeMonic();
        if (nzPoly.deg() >= 1) {
            std::vector<UPoly> irreds = factorOverQ(nzPoly, budget);
            if (budget && !budget->ok()) {
                out.reason = "budget exhausted during characteristic factorization";
                return out;
            }
            struct FactorMult
            {
                UPoly q;
                int mult = 0;
            };
            std::vector<FactorMult> fms;
            for (const UPoly &ir : irreds) {
                bool found = false;
                for (auto &fm : fms) {
                    if (fm.q == ir) {
                        fm.mult += 1;
                        found = true;
                        break;
                    }
                }
                if (!found)
                    fms.push_back(FactorMult{ir, 1});
            }
            const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
            for (const auto &fm : fms) {
                if (fm.q.deg() == 1) {
                    const Expr r = c.number(-fm.q.coeff(0));
                    const Expr rPowN = (r == c.one()) ? c.one() : c.pow(r, n);
                    for (int m = 0; m < fm.mult; ++m) {
                        const Expr nPowM =
                            (m == 0) ? c.one()
                                     : c.pow(n, c.number(static_cast<std::int64_t>(m)));
                        basis.push_back(c.mul({nPowM, rPowN}));
                    }
                } else if (fm.q.deg() == 2) {
                    const Rational bRat = fm.q.coeff(1);
                    const Rational dRat = fm.q.coeff(0);
                    const Rational disc =
                        bRat * bRat - Rational(std::int64_t{4}) * dRat;
                    if (disc.signum() > 0) {
                        const Expr sqrtDisc =
                            c.simplify(c.pow(c.number(disc), half));
                        const Expr negHalfB = c.number(
                            -bRat * Rational(std::int64_t{1}, BigInt(2)));
                        const Expr r1 =
                            c.add({negHalfB, c.mul({half, sqrtDisc})});
                        const Expr r2 =
                            c.add({negHalfB, c.neg(c.mul({half, sqrtDisc}))});
                        for (int m = 0; m < fm.mult; ++m) {
                            const Expr nPowM =
                                (m == 0)
                                    ? c.one()
                                    : c.pow(n, c.number(static_cast<std::int64_t>(m)));
                            basis.push_back(c.mul({nPowM, c.pow(r1, n)}));
                            basis.push_back(c.mul({nPowM, c.pow(r2, n)}));
                        }
                    } else if (disc.signum() < 0 && dRat.signum() > 0) {
                        const Expr r = c.simplify(c.pow(c.number(dRat), half));
                        const Expr invR = c.simplify(c.pow(
                            c.number(dRat),
                            c.number(Rational(std::int64_t{-1}, BigInt(2)))));
                        const Expr cosW = c.simplify(c.mul(
                            {c.number(-bRat * Rational(std::int64_t{1}, BigInt(2))),
                             invR}));
                        const Expr omega = c.simplify(c.func("acos", cosW));
                        const Expr rPowN =
                            (r == c.one()) ? c.one() : c.pow(r, n);
                        const Expr cosWn = c.func("cos", c.mul({omega, n}));
                        const Expr sinWn = c.func("sin", c.mul({omega, n}));
                        for (int m = 0; m < fm.mult; ++m) {
                            const Expr nPowM =
                                (m == 0)
                                    ? c.one()
                                    : c.pow(n, c.number(static_cast<std::int64_t>(m)));
                            basis.push_back(c.mul({nPowM, rPowN, cosWn}));
                            basis.push_back(c.mul({nPowM, rPowN, sinWn}));
                        }
                    }
                }
            }
        }
    }

    // Symbolic root fallback when P(z) contains parameters.
    if (basis.size() != orderK) {
        basis.clear();
        const std::vector<Expr> roots = solveSymbolic(c, pZ, z, budget);
        for (const Expr &r : roots) {
            if (c.isZero(r))
                continue;
            // Determine multiplicity of root r in P(z).
            int mult = 0;
            Expr curP = pZ;
            while (mult < static_cast<int>(orderK)) {
                const Expr val = c.simplify(c.subs(curP, z, r));
                if (val.isNull() || !c.isZero(val))
                    break;
                ++mult;
                curP = c.diff(curP, z);
            }
            if (mult == 0)
                mult = 1;
            const Expr rPowN = (r == c.one()) ? c.one() : c.pow(r, n);
            for (int m = 0; m < mult; ++m) {
                const Expr nPowM =
                    (m == 0) ? c.one()
                             : c.pow(n, c.number(static_cast<std::int64_t>(m)));
                basis.push_back(c.mul({nPowM, rPowN}));
            }
        }
    }

    if (basis.size() != orderK) {
        out.reason = "unable to construct complete homogeneous recurrence basis";
        return out;
    }

    std::vector<Expr> solTerms;
    for (std::size_t i = 0; i < orderK; ++i) {
        const Expr ci = c.symbol("C" + std::to_string(i + 1));
        solTerms.push_back(c.mul({ci, basis[i]}));
    }

    if (!c.isZero(rhs)) {
        std::vector<Expr> zeroInits(orderK, c.zero());
        const RsolveResult part =
            rsolveIVP(c, coeffs, rhs, n, zeroInits, budget);
        if (!part.proved()) {
            out.reason = part.reason;
            return out;
        }
        solTerms.push_back(part.y);
    }

    const Expr ySol = c.simplify(c.add(solTerms));
    std::vector<Expr> trimmedCoeffs(coeffs.begin(),
                                    coeffs.begin() +
                                        static_cast<std::ptrdiff_t>(orderK + 1));
    if (!certifyRecurrence(c, trimmedCoeffs, rhs, ySol, n)) {
        out.reason = "general recurrence solution failed residual certificate";
        return out;
    }

    out.y = ySol;
    out.status = RsolveResult::Status::ProvedSymbolic;
    return out;
}

} // namespace numkit::cas
