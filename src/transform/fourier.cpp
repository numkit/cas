// src/transform/fourier.cpp — symbolic bilateral Fourier and inverse Fourier transforms.
#include <numkit/cas/transform/fourier.hpp>

#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/poly/upoly.hpp>

#include <cmath>
#include <cstdint>
#include <string>
#include <vector>

namespace numkit::cas {
namespace {

bool checkFourierBudget(Ctx &c, Budget *budget, std::string &reason)
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

bool dependsOn(const Ctx &c, Expr e, Expr var)
{
    if (e.isNull())
        return false;
    if (e == var)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i) {
        if (dependsOn(c, c.child(e, i), var))
            return true;
    }
    return false;
}

bool mentionsSymbolName(const Ctx &c, Expr e, const std::string &name)
{
    if (e.isNull())
        return false;
    if (c.kind(e) == NodeKind::Symbol && c.symbolName(e) == name)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i) {
        if (mentionsSymbolName(c, c.child(e, i), name))
            return true;
    }
    return false;
}

// Decompose an expression `e` involving the imaginary unit symbol `I` (I^2 = -1)
// into real and imaginary parts: e = reOut + I * imOut.
bool splitComplexI(Ctx &c, Expr e, Expr &reOut, Expr &imOut)
{
    if (e.isNull())
        return false;
    if (!mentionsSymbolName(c, e, "I")) {
        reOut = e;
        imOut = c.zero();
        return true;
    }
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::RootOf:
        reOut = e;
        imOut = c.zero();
        return true;
    case NodeKind::Symbol:
        if (c.symbolName(e) == "I") {
            reOut = c.zero();
            imOut = c.one();
        } else {
            reOut = e;
            imOut = c.zero();
        }
        return true;
    case NodeKind::Add: {
        std::vector<Expr> reTerms, imTerms;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            Expr r, m;
            if (!splitComplexI(c, c.child(e, i), r, m))
                return false;
            if (!c.isZero(r))
                reTerms.push_back(r);
            if (!c.isZero(m))
                imTerms.push_back(m);
        }
        reOut = reTerms.empty() ? c.zero() : c.simplify(c.add(reTerms));
        imOut = imTerms.empty() ? c.zero() : c.simplify(c.add(imTerms));
        return true;
    }
    case NodeKind::Mul: {
        Expr curRe = c.one();
        Expr curIm = c.zero();
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            Expr r, m;
            if (!splitComplexI(c, c.child(e, i), r, m))
                return false;
            const Expr nextRe =
                c.add({c.mul({curRe, r}), c.neg(c.mul({curIm, m}))});
            const Expr nextIm = c.add({c.mul({curRe, m}), c.mul({curIm, r})});
            curRe = nextRe;
            curIm = nextIm;
        }
        reOut = c.simplify(curRe);
        imOut = c.simplify(curIm);
        return true;
    }
    case NodeKind::Pow: {
        const Expr base = c.child(e, 0);
        const Expr expNode = c.child(e, 1);
        if (c.kind(expNode) != NodeKind::Number ||
            !(c.numberValue(expNode).den() == BigInt(1)))
            return false;
        std::int64_t k = 0;
        if (!c.numberValue(expNode).num().fitsInt64(k) || std::abs(k) > 12)
            return false;
        Expr bRe, bIm;
        if (!splitComplexI(c, base, bRe, bIm))
            return false;
        const std::int64_t absK = std::abs(k);
        Expr pRe = c.one();
        Expr pIm = c.zero();
        for (std::int64_t i = 0; i < absK; ++i) {
            const Expr nextRe =
                c.add({c.mul({pRe, bRe}), c.neg(c.mul({pIm, bIm}))});
            const Expr nextIm = c.add({c.mul({pRe, bIm}), c.mul({pIm, bRe})});
            pRe = nextRe;
            pIm = nextIm;
        }
        pRe = c.simplify(pRe);
        pIm = c.simplify(pIm);
        if (k >= 0) {
            reOut = pRe;
            imOut = pIm;
            return true;
        }
        const Expr normSq = c.simplify(
            c.add({c.pow(pRe, c.number(2)), c.pow(pIm, c.number(2))}));
        if (c.isZero(normSq))
            return false;
        reOut = c.simplify(c.div(pRe, normSq));
        imOut = c.simplify(c.neg(c.div(pIm, normSq)));
        return true;
    }
    case NodeKind::Func: {
        if (c.funcName(e) == "exp") {
            Expr aRe, aIm;
            if (!splitComplexI(c, c.child(e, 0), aRe, aIm))
                return false;
            const Expr mag = c.isZero(aRe) ? c.one() : c.func("exp", aRe);
            reOut = c.simplify(c.mul({mag, c.func("cos", aIm)}));
            imOut = c.simplify(c.mul({mag, c.func("sin", aIm)}));
            return true;
        }
        return false;
    }
    }
    return false;
}

// Match linear form `a * u + b` where `a != 0` and `a, b` do not depend on `u`.
bool matchLinearInVar(Ctx &c, Expr e, Expr u, Expr &aOut, Expr &bOut)
{
    if (c.kind(u) != NodeKind::Symbol)
        return false;
    const Expr expd = c.expand(e);
    if (!dependsOn(c, expd, u))
        return false;
    const Expr rawDa = c.diff(expd, u);
    if (rawDa.isNull())
        return false;
    const Expr da = c.simplify(rawDa);
    if (dependsOn(c, da, u) || c.isZero(da))
        return false;
    aOut = da;
    bOut = c.simplify(c.subs(expd, u, c.zero()));
    return !dependsOn(c, bOut, u);
}

// Match `-a * u^2` with `a > 0` independent of `u`.
bool matchNegQuadInVar(Ctx &c, Expr e, Expr u, Expr &aOut)
{
    if (c.kind(u) != NodeKind::Symbol)
        return false;
    const Expr expd = c.expand(e);
    const Expr b0 = c.simplify(c.subs(expd, u, c.zero()));
    if (!c.isZero(b0))
        return false;
    const Expr rawD1 = c.diff(expd, u);
    if (rawD1.isNull())
        return false;
    const Expr d1 = c.simplify(rawD1);
    if (!c.isZero(c.simplify(c.subs(d1, u, c.zero()))))
        return false;
    const Expr rawD2 = c.diff(d1, u);
    if (rawD2.isNull())
        return false;
    const Expr d2 = c.simplify(rawD2);
    if (dependsOn(c, d2, u))
        return false;
    const Expr a = c.simplify(
        c.mul({c.number(Rational(std::int64_t{-1}, BigInt(2))), d2}));
    if (!c.isAssumedPositive(a))
        return false;
    aOut = a;
    return true;
}

// Match `-a * abs(u)` with `a > 0` independent of `u`.
bool matchNegAbsInVar(Ctx &c, Expr e, Expr u, Expr &aOut)
{
    if (c.kind(e) == NodeKind::Mul) {
        std::vector<Expr> cFacs;
        bool hasAbsU = false;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr ch = c.child(e, i);
            if (!hasAbsU && c.kind(ch) == NodeKind::Func &&
                c.funcName(ch) == "abs" &&
                (c.child(ch, 0) == u || c.child(ch, 0) == c.neg(u))) {
                hasAbsU = true;
            } else if (!dependsOn(c, ch, u)) {
                cFacs.push_back(ch);
            } else {
                return false;
            }
        }
        if (hasAbsU) {
            const Expr negCoef = cFacs.empty() ? c.one() : c.mul(cFacs);
            const Expr a = c.simplify(c.neg(negCoef));
            if (c.isAssumedPositive(a)) {
                aOut = a;
                return true;
            }
        }
    }
    return false;
}

bool fourierRealTerm(Ctx &c, Expr term, Expr u, Expr v, int expSign,
                     Budget *budget, Expr &reOut, Expr &imOut,
                     std::string &reason);

bool fourierRealSum(Ctx &c, Expr f, Expr u, Expr v, int expSign, Budget *budget,
                    Expr &reOut, Expr &imOut, std::string &reason)
{
    if (!checkFourierBudget(c, budget, reason))
        return false;
    if (c.kind(f) != NodeKind::Add &&
        fourierRealTerm(c, f, u, v, expSign, budget, reOut, imOut, reason)) {
        return true;
    }
    const Expr expd = c.expand(f);
    if (c.kind(expd) == NodeKind::Add) {
        std::vector<Expr> reTerms, imTerms;
        for (std::size_t i = 0; i < c.childCount(expd); ++i) {
            Expr r, m;
            if (!fourierRealTerm(c, c.child(expd, i), u, v, expSign, budget, r,
                                 m, reason))
                return false;
            if (!c.isZero(r))
                reTerms.push_back(r);
            if (!c.isZero(m))
                imTerms.push_back(m);
        }
        reOut = reTerms.empty() ? c.zero() : c.simplify(c.add(reTerms));
        imOut = imTerms.empty() ? c.zero() : c.simplify(c.add(imTerms));
        return true;
    }
    return fourierRealTerm(c, expd, u, v, expSign, budget, reOut, imOut, reason);
}

bool fourierRealTerm(Ctx &c, Expr term, Expr u, Expr v, int expSign,
                     Budget *budget, Expr &reOut, Expr &imOut,
                     std::string &reason)
{
    if (!checkFourierBudget(c, budget, reason))
        return false;

    const Expr piSym = c.symbol("pi");
    const Expr two = c.number(2);

    // 1. Constant with respect to `u`: int_{-inf}^{inf} C * exp(sigma*i*v*u) du = 2*pi*C*dirac(v).
    if (!dependsOn(c, term, u)) {
        reOut = c.simplify(c.mul({two, piSym, term, c.func("dirac", v)}));
        imOut = c.zero();
        return true;
    }

    std::vector<Expr> facs;
    if (c.kind(term) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(term); ++i)
            facs.push_back(c.child(term, i));
    } else {
        facs.push_back(term);
    }

    std::vector<Expr> constFacs;
    std::vector<Expr> varFacs;
    for (const Expr &fac : facs) {
        if (!dependsOn(c, fac, u))
            constFacs.push_back(fac);
        else
            varFacs.push_back(fac);
    }
    const Expr constCoef = constFacs.empty() ? c.one() : c.mul(constFacs);
    const Expr core = varFacs.size() == 1 ? varFacs[0] : c.mul(varFacs);

    auto scaleResult = [&](Expr r, Expr m) {
        reOut = c.simplify(c.mul({constCoef, r}));
        imOut = c.simplify(c.mul({constCoef, m}));
    };

    // 2. Dirac impulse: g(u) * dirac(a*u + b) -> (1/|a|) * g(-b/a) * exp(sigma*i*v*(-b/a)).
    for (std::size_t i = 0; i < varFacs.size(); ++i) {
        if (c.kind(varFacs[i]) == NodeKind::Func &&
            c.funcName(varFacs[i]) == "dirac") {
            Expr aLin, bLin;
            if (matchLinearInVar(c, c.child(varFacs[i], 0), u, aLin, bLin)) {
                Expr absA = aLin;
                if (c.isAssumedNegative(aLin))
                    absA = c.neg(aLin);
                else if (!c.isAssumedPositive(aLin))
                    absA = c.func("abs", aLin);
                const Expr u0 = c.simplify(c.neg(c.div(bLin, aLin)));
                std::vector<Expr> restFacs;
                for (std::size_t j = 0; j < varFacs.size(); ++j) {
                    if (j != i)
                        restFacs.push_back(varFacs[j]);
                }
                const Expr gAtU0 =
                    restFacs.empty()
                        ? c.one()
                        : c.simplify(c.subs(c.mul(restFacs), u, u0));
                const Expr scale = c.div(gAtU0, absA);
                if (c.isZero(u0)) {
                    scaleResult(scale, c.zero());
                    return true;
                }
                const Expr phase = c.mul({u0, v});
                const Expr r = c.mul({scale, c.func("cos", phase)});
                const Expr m = c.mul(
                    {c.number(expSign), scale, c.func("sin", phase)});
                scaleResult(r, m);
                return true;
            }
        }
    }

    // 3. Sinc kernel: sin(a*u) / u -> pi * heaviside(a - abs(v)),
    //    Fejer kernel: (1 - cos(a*u)) / u^2 -> (pi/2)*(a - abs(v))*heaviside(a - abs(v)),
    //    and rectangular pulse heaviside(a - abs(u)) -> 2 * sin(a*v) / v.
    if (varFacs.size() == 2) {
        int uInvIdx = -1, uInv2Idx = -1, sinIdx = -1, oneMinusCosIdx = -1;
        for (int i = 0; i < 2; ++i) {
            const Expr &f = varFacs[static_cast<std::size_t>(i)];
            if (c.kind(f) == NodeKind::Pow && c.child(f, 0) == u &&
                c.child(f, 1) == c.number(-1)) {
                uInvIdx = i;
            } else if (c.kind(f) == NodeKind::Pow && c.child(f, 0) == u &&
                       c.child(f, 1) == c.number(-2)) {
                uInv2Idx = i;
            } else if (c.kind(f) == NodeKind::Func && c.funcName(f) == "sin") {
                sinIdx = i;
            } else if (c.kind(f) == NodeKind::Add && c.childCount(f) == 2) {
                oneMinusCosIdx = i;
            }
        }
        if (uInvIdx >= 0 && sinIdx >= 0) {
            Expr aLin, bLin;
            if (matchLinearInVar(
                    c, c.child(varFacs[static_cast<std::size_t>(sinIdx)], 0), u,
                    aLin, bLin) &&
                c.isZero(bLin) && c.isAssumedPositive(aLin)) {
                const Expr box = c.mul(
                    {piSym,
                     c.func("heaviside",
                            c.add({aLin, c.neg(c.func("abs", v))}))});
                scaleResult(box, c.zero());
                return true;
            }
        }
        if (uInv2Idx >= 0 && oneMinusCosIdx >= 0) {
            const Expr addNode =
                varFacs[static_cast<std::size_t>(oneMinusCosIdx)];
            const Expr diffFromOne = c.simplify(c.add({c.one(), c.neg(addNode)}));
            if (c.kind(diffFromOne) == NodeKind::Func &&
                c.funcName(diffFromOne) == "cos") {
                Expr aLin, bLin;
                if (matchLinearInVar(c, c.child(diffFromOne, 0), u, aLin,
                                     bLin) &&
                    c.isZero(bLin)) {
                    if (c.isAssumedNegative(aLin))
                        aLin = c.neg(aLin);
                    if (c.isAssumedPositive(aLin)) {
                        const Expr aMinusAbsV =
                            c.add({aLin, c.neg(c.func("abs", v))});
                        const Expr tri = c.mul(
                            {c.number(Rational(1, BigInt(2))), piSym,
                             aMinusAbsV, c.func("heaviside", aMinusAbsV)});
                        scaleResult(tri, c.zero());
                        return true;
                    }
                }
            }
        }
    }
    if (varFacs.size() == 1 && c.kind(core) == NodeKind::Func &&
        c.funcName(core) == "heaviside") {
        // heaviside(a - abs(u))
        const Expr hArg = c.child(core, 0);
        const Expr aConst = c.simplify(c.add({hArg, c.func("abs", u)}));
        if (!dependsOn(c, aConst, u) && c.isAssumedPositive(aConst)) {
            const Expr sincVal =
                c.div(c.mul({two, c.func("sin", c.mul({aConst, v}))}), v);
            scaleResult(sincVal, c.zero());
            return true;
        }
    }

    // 4. Shifted sign(u + a) (used by boxcar dual sign(u + a) - sign(u - a)
    //    and Hilbert transform of sign(u)):
    //    int sign(u + a) * exp(sigma*i*v*u) du = exp(-sigma*i*a*v) * (2*sigma*i / v)
    //      = (2 * sin(a*v) / v) + I * (2 * sigma * cos(a*v) / v).
    if (varFacs.size() == 1 && c.kind(core) == NodeKind::Func &&
        c.funcName(core) == "sign") {
        Expr aLin, bLin;
        if (matchLinearInVar(c, c.child(core, 0), u, aLin, bLin) &&
            aLin == c.one()) {
            if (c.isZero(bLin)) {
                scaleResult(c.zero(),
                            c.div(c.number(2 * expSign), v));
                return true;
            }
            const Expr av = c.mul({bLin, v});
            const Expr r = c.div(c.mul({two, c.func("sin", av)}), v);
            const Expr m =
                c.div(c.mul({c.number(2 * expSign), c.func("cos", av)}), v);
            scaleResult(r, m);
            return true;
        }
    }
    // Principal value 1/u -> I * sigma * pi * sign(v)
    if (varFacs.size() == 1 && c.kind(core) == NodeKind::Pow &&
        c.child(core, 0) == u && c.child(core, 1) == c.number(-1)) {
        scaleResult(c.zero(),
                    c.mul({c.number(expSign), piSym, c.func("sign", v)}));
        return true;
    }

    // 5. Trigonometric modulation: g(u) * cos(w0*u) or g(u) * sin(w0*u).
    for (std::size_t i = 0; i < varFacs.size(); ++i) {
        if (c.kind(varFacs[i]) == NodeKind::Func &&
            (c.funcName(varFacs[i]) == "cos" ||
             c.funcName(varFacs[i]) == "sin")) {
            const bool isCos = (c.funcName(varFacs[i]) == "cos");
            Expr w0, b0;
            if (matchLinearInVar(c, c.child(varFacs[i], 0), u, w0, b0) &&
                c.isZero(b0)) {
                std::vector<Expr> restFacs;
                for (std::size_t j = 0; j < varFacs.size(); ++j) {
                    if (j != i)
                        restFacs.push_back(varFacs[j]);
                }
                const Expr gRest =
                    restFacs.empty() ? c.one() : c.mul(restFacs);
                const Expr vTmp = c.symbol("_fourier_v_mod");
                Expr rG, mG;
                if (fourierRealTerm(c, gRest, u, vTmp, expSign, budget, rG, mG,
                                    reason)) {
                    const Expr vMinus = c.add({v, c.neg(w0)});
                    const Expr vPlus = c.add({v, w0});
                    const Expr rMinus = c.subs(rG, vTmp, vMinus);
                    const Expr rPlus = c.subs(rG, vTmp, vPlus);
                    const Expr mMinus = c.subs(mG, vTmp, vMinus);
                    const Expr mPlus = c.subs(mG, vTmp, vPlus);
                    const Expr half = c.number(Rational(1, BigInt(2)));
                    if (isCos) {
                        scaleResult(c.mul({half, c.add({rMinus, rPlus})}),
                                    c.mul({half, c.add({mMinus, mPlus})}));
                    } else {
                        const Expr sgnHalf =
                            c.number(Rational(expSign, BigInt(2)));
                        scaleResult(
                            c.mul({sgnHalf, c.add({mPlus, c.neg(mMinus)})}),
                            c.mul({sgnHalf, c.add({rMinus, c.neg(rPlus)})}));
                    }
                    return true;
                }
            }
        }
    }

    // 6. Hyperbolic secant and cosecant kernels:
    //    sech(a*u) -> (pi/a) * sech(pi*v / (2*a))
    //    sech(a*u)^2 -> (pi*v / a^2) * csch(pi*v / (2*a))
    //    u * csch(a*u) -> (pi^2 / (2*a^2)) * sech(pi*v / (2*a))^2
    {
        auto matchHypKernel = [&](Expr f, std::string &hFn, Expr &aVal,
                                  int &hPow) -> bool {
            Expr inner = f;
            hPow = 1;
            if (c.kind(f) == NodeKind::Pow &&
                c.kind(c.child(f, 1)) == NodeKind::Number) {
                std::int64_t p = 0;
                if (c.numberValue(c.child(f, 1)).den() == BigInt(1) &&
                    c.numberValue(c.child(f, 1)).num().fitsInt64(p)) {
                    inner = c.child(f, 0);
                    hPow = static_cast<int>(p);
                } else {
                    return false;
                }
            }
            if (c.kind(inner) != NodeKind::Func)
                return false;
            const std::string &fn = c.funcName(inner);
            Expr b0;
            if (!matchLinearInVar(c, c.child(inner, 0), u, aVal, b0) ||
                !c.isZero(b0))
                return false;
            if (c.isAssumedNegative(aVal))
                aVal = c.neg(aVal);
            if (!c.isAssumedPositive(aVal))
                return false;
            if (fn == "sech") {
                hFn = "sech";
                return true;
            }
            if (fn == "cosh" && hPow < 0) {
                hFn = "sech";
                hPow = -hPow;
                return true;
            }
            if (fn == "csch" && hPow == 1) {
                hFn = "csch";
                return true;
            }
            if (fn == "sinh" && hPow == -1) {
                hFn = "csch";
                hPow = 1;
                return true;
            }
            return false;
        };
        std::string hFn;
        Expr aVal;
        int hPow = 0;
        if (varFacs.size() == 1 && matchHypKernel(core, hFn, aVal, hPow) &&
            hFn == "sech" && (hPow == 1 || hPow == 2)) {
            const Expr dualArg =
                c.div(c.mul({piSym, v}), c.mul({two, aVal}));
            if (hPow == 1) {
                scaleResult(
                    c.mul({c.div(piSym, aVal), c.func("sech", dualArg)}),
                    c.zero());
                return true;
            }
            scaleResult(
                c.mul({c.div(c.mul({piSym, v}), c.pow(aVal, two)),
                       c.func("csch", dualArg)}),
                c.zero());
            return true;
        }
        if (varFacs.size() == 2) {
            int uIdx = (varFacs[0] == u) ? 0 : ((varFacs[1] == u) ? 1 : -1);
            if (uIdx >= 0 &&
                matchHypKernel(varFacs[static_cast<std::size_t>(1 - uIdx)],
                               hFn, aVal, hPow) &&
                hFn == "csch" && hPow == 1) {
                const Expr dualArg =
                    c.div(c.mul({piSym, v}), c.mul({two, aVal}));
                const Expr sechSq = c.pow(c.func("sech", dualArg), two);
                const Expr coef =
                    c.div(c.pow(piSym, two), c.mul({two, c.pow(aVal, two)}));
                scaleResult(c.mul({coef, sechSq}), c.zero());
                return true;
            }
        }
    }

    // 7. Frequency differentiation for u^n * g(u) (n >= 1) when g(u) contains
    //    an exponential decay factor (Gaussian, two-sided exp, or causal exp).
    {
        std::int64_t uPow = 0;
        std::vector<Expr> gFacs;
        bool hasExpDecay = false;
        for (const Expr &fac : varFacs) {
            if (fac == u) {
                uPow += 1;
                continue;
            }
            if (c.kind(fac) == NodeKind::Pow && c.child(fac, 0) == u &&
                c.kind(c.child(fac, 1)) == NodeKind::Number) {
                const Rational &re = c.numberValue(c.child(fac, 1));
                std::int64_t k = 0;
                if (re.den() == BigInt(1) && re.num().fitsInt64(k) && k >= 1 &&
                    k <= 8) {
                    uPow += k;
                    continue;
                }
            }
            if (c.kind(fac) == NodeKind::Func && c.funcName(fac) == "exp")
                hasExpDecay = true;
            gFacs.push_back(fac);
        }
        if (uPow >= 1 && uPow <= 8 && hasExpDecay && !gFacs.empty()) {
            Expr rG, mG;
            if (fourierRealTerm(c, c.mul(gFacs), u, v, expSign, budget, rG, mG,
                                reason)) {
                for (std::int64_t k = 0; k < uPow; ++k) {
                    const Expr dr = c.diff(rG, v);
                    const Expr dm = c.diff(mG, v);
                    rG = c.simplify(c.mul({c.number(expSign), dm}));
                    mG = c.simplify(c.mul({c.number(-expSign), dr}));
                }
                scaleResult(rG, mG);
                return true;
            }
        }
    }

    // 8. Exponential kernels:
    //    a) Gaussian exp(-a*u^2) -> sqrt(pi/a) * exp(-v^2 / (4*a))
    //    b) Two-sided exponential abs(u)^m * sign(u)^s * exp(-a*abs(u))
    //    c) Causal / anti-causal exponential exp(-a*u)*heaviside(u), exp(a*u)*heaviside(-u)
    {
        std::vector<Expr> expArgs;
        std::int64_t absPow = 0;
        bool hasSignU = false;
        int heavisideDir = 0; // +1 for heaviside(u), -1 for heaviside(-u)
        bool okExpShape = true;
        for (const Expr &fac : varFacs) {
            if (c.kind(fac) == NodeKind::Func && c.funcName(fac) == "exp") {
                expArgs.push_back(c.child(fac, 0));
            } else if (c.kind(fac) == NodeKind::Func &&
                       c.funcName(fac) == "abs" &&
                       (c.child(fac, 0) == u || c.child(fac, 0) == c.neg(u))) {
                absPow += 1;
            } else if (c.kind(fac) == NodeKind::Pow &&
                       c.kind(c.child(fac, 0)) == NodeKind::Func &&
                       c.funcName(c.child(fac, 0)) == "abs" &&
                       (c.child(c.child(fac, 0), 0) == u ||
                        c.child(c.child(fac, 0), 0) == c.neg(u)) &&
                       c.kind(c.child(fac, 1)) == NodeKind::Number) {
                std::int64_t k = 0;
                if (c.numberValue(c.child(fac, 1)).den() == BigInt(1) &&
                    c.numberValue(c.child(fac, 1)).num().fitsInt64(k) &&
                    k >= 1 && k <= 6) {
                    absPow += k;
                } else {
                    okExpShape = false;
                    break;
                }
            } else if (!hasSignU && c.kind(fac) == NodeKind::Func &&
                       c.funcName(fac) == "sign" && c.child(fac, 0) == u) {
                hasSignU = true;
            } else if (heavisideDir == 0 && c.kind(fac) == NodeKind::Func &&
                       c.funcName(fac) == "heaviside") {
                if (c.child(fac, 0) == u)
                    heavisideDir = +1;
                else if (c.child(fac, 0) == c.neg(u))
                    heavisideDir = -1;
                else {
                    okExpShape = false;
                    break;
                }
            } else {
                okExpShape = false;
                break;
            }
        }
        if (okExpShape && !expArgs.empty()) {
            const Expr sumExp =
                expArgs.size() == 1 ? expArgs[0] : c.simplify(c.add(expArgs));
            Expr aVal;
            // 8a. Gaussian exp(-a * u^2)
            if (absPow == 0 && !hasSignU && heavisideDir == 0 &&
                matchNegQuadInVar(c, sumExp, u, aVal)) {
                const Expr half = c.number(Rational(1, BigInt(2)));
                const Expr coef = c.pow(c.div(piSym, aVal), half);
                const Expr gaussV = c.func(
                    "exp",
                    c.neg(c.div(c.pow(v, two), c.mul({c.number(4), aVal}))));
                scaleResult(c.mul({coef, gaussV}), c.zero());
                return true;
            }
            // 8b. Two-sided exponential abs(u)^m * sign(u)^s * exp(-a * abs(u))
            if (heavisideDir == 0 && matchNegAbsInVar(c, sumExp, u, aVal)) {
                const Expr denom = c.add({c.pow(aVal, two), c.pow(v, two)});
                if (!hasSignU && absPow == 0) {
                    scaleResult(c.div(c.mul({two, aVal}), denom), c.zero());
                    return true;
                }
                if (!hasSignU && absPow == 1) {
                    const Expr num =
                        c.mul({two, c.add({c.pow(aVal, two), c.neg(c.pow(v, two))})});
                    scaleResult(c.div(num, c.pow(denom, two)), c.zero());
                    return true;
                }
                if (hasSignU && absPow == 0) {
                    scaleResult(
                        c.zero(),
                        c.div(c.mul({c.number(2 * expSign), v}), denom));
                    return true;
                }
                if (hasSignU && absPow == 1) {
                    // u * exp(-a * abs(u)): derivative of 2*a/(a^2 + v^2)
                    const Expr num =
                        c.mul({c.number(4 * expSign), aVal, v});
                    scaleResult(c.zero(), c.div(num, c.pow(denom, two)));
                    return true;
                }
            }
            // 8c. Causal / anti-causal exponential exp(\mp a*u) * heaviside(\pm u)
            Expr aLin, bLin;
            if (absPow == 0 && !hasSignU && heavisideDir != 0 &&
                matchLinearInVar(c, sumExp, u, aLin, bLin) && c.isZero(bLin)) {
                const Expr decayRate =
                    heavisideDir > 0 ? c.simplify(c.neg(aLin)) : aLin;
                if (c.isAssumedPositive(decayRate)) {
                    const Expr denom =
                        c.add({c.pow(decayRate, two), c.pow(v, two)});
                    const Expr r = c.div(decayRate, denom);
                    const Expr m = c.div(
                        c.mul({c.number(heavisideDir * expSign), v}), denom);
                    scaleResult(r, m);
                    return true;
                }
            }
        }
    }

    // 9. Rational functions R(u) via polynomial division (if improper) and
    //    upper-half-plane Jordan contour integration.
    {
        UPoly N, D;
        if (toRational(c, core, u, N, D) && !D.isConst() &&
            N.deg() >= D.deg()) {
            UPoly Q, R;
            UPoly::divMod(N, D, Q, R);
            if (Q.deg() <= 0) {
                const Expr decomp = c.add(
                    {toExpr(c, Q, u),
                     c.div(toExpr(c, R, u), toExpr(c, D, u))});
                Expr rSub, mSub;
                if (fourierRealSum(c, decomp, u, v, expSign, budget, rSub, mSub,
                                   reason)) {
                    scaleResult(rSub, mSub);
                    return true;
                }
            }
        }

        const Expr vPos = c.symbol("_fourier_vpos");
        c.assume(vPos, AssumeDomain::Positive);
        const Expr negInf = c.neg(c.symbol("inf"));
        const Expr posInf = c.symbol("inf");

        const Expr coreNeg = c.subs(core, u, c.neg(u));
        const bool isEven =
            c.isZero(c.simplify(c.add({core, c.neg(coreNeg)})));
        const bool isOdd =
            c.isZero(c.simplify(c.add({core, coreNeg})));

        const Expr absV = c.isAssumedNonNegative(v)
                              ? v
                              : (c.isAssumedNegative(v) ? c.neg(v)
                                                        : c.func("abs", v));
        const Expr sgnV = c.isAssumedPositive(v)
                              ? c.one()
                              : (c.isAssumedNegative(v) ? c.number(-1)
                                                        : c.func("sign", v));

        if (isEven) {
            const DefiniteIntegral intCos = definiteIntegrate(
                c, c.mul({core, c.func("cos", c.mul({vPos, u}))}), u, negInf,
                posInf, budget);
            c.assume(vPos, AssumeDomain::Any);
            if (intCos.proved()) {
                const Expr r = c.subs(intCos.value, vPos, absV);
                scaleResult(r, c.zero());
                return true;
            }
        } else if (isOdd) {
            const DefiniteIntegral intSin = definiteIntegrate(
                c, c.mul({core, c.func("sin", c.mul({vPos, u}))}), u, negInf,
                posInf, budget);
            c.assume(vPos, AssumeDomain::Any);
            if (intSin.proved()) {
                const Expr sVal = c.subs(intSin.value, vPos, absV);
                const Expr m =
                    c.mul({c.number(expSign), sgnV, sVal});
                scaleResult(c.zero(), m);
                return true;
            }
        } else {
            const DefiniteIntegral intCos = definiteIntegrate(
                c, c.mul({core, c.func("cos", c.mul({vPos, u}))}), u, negInf,
                posInf, budget);
            const DefiniteIntegral intSin = definiteIntegrate(
                c, c.mul({core, c.func("sin", c.mul({vPos, u}))}), u, negInf,
                posInf, budget);
            c.assume(vPos, AssumeDomain::Any);
            if (intCos.proved() && intSin.proved()) {
                const Expr r = c.subs(intCos.value, vPos, absV);
                const Expr m = c.mul({c.number(expSign), sgnV,
                                      c.subs(intSin.value, vPos, absV)});
                scaleResult(r, m);
                return true;
            }
        }
    }

    reason = "unsupported Fourier transform kernel";
    return false;
}

// Compute int_{-inf}^{inf} f(u) * exp(expSign * I * v * u) du = reOut + I * imOut,
// where `f` may contain the imaginary unit `I`.
bool fourierComplexExpr(Ctx &c, Expr f, Expr u, Expr v, int expSign,
                        Budget *budget, Expr &reOut, Expr &imOut,
                        std::string &reason)
{
    Expr fRe, fIm;
    if (!splitComplexI(c, f, fRe, fIm)) {
        reason = "unable to separate real and imaginary parts";
        return false;
    }
    Expr r1 = c.zero(), m1 = c.zero();
    Expr r2 = c.zero(), m2 = c.zero();
    if (!c.isZero(fRe)) {
        if (!fourierRealSum(c, fRe, u, v, expSign, budget, r1, m1, reason))
            return false;
    }
    if (!c.isZero(fIm)) {
        if (!fourierRealSum(c, fIm, u, v, expSign, budget, r2, m2, reason))
            return false;
    }
    // (r1 + I*m1) + I*(r2 + I*m2) = (r1 - m2) + I*(m1 + r2)
    reOut = c.simplify(c.add({r1, c.neg(m2)}));
    imOut = c.simplify(c.add({m1, r2}));
    return true;
}

// Fold `K(t) + K(t)*sign(t) -> 2 * K|_{|t|->t} * heaviside(t)` and
// `K(t) - K(t)*sign(t) -> 2 * K|_{|t|->-t} * heaviside(-t)` across additive terms.
Expr canonicalizeHeavisideExp(Ctx &c, Expr e, Expr t)
{
    auto stripSignT = [&](Expr term, Expr &baseOut) -> bool {
        if (c.kind(term) == NodeKind::Func && c.funcName(term) == "sign" &&
            c.child(term, 0) == t) {
            baseOut = c.one();
            return true;
        }
        if (c.kind(term) != NodeKind::Mul)
            return false;
        std::vector<Expr> others;
        bool found = false;
        for (std::size_t i = 0; i < c.childCount(term); ++i) {
            const Expr ch = c.child(term, i);
            if (!found && c.kind(ch) == NodeKind::Func &&
                c.funcName(ch) == "sign" && c.child(ch, 0) == t) {
                found = true;
            } else {
                others.push_back(ch);
            }
        }
        if (!found)
            return false;
        baseOut = others.empty() ? c.one() : c.mul(others);
        return true;
    };

    const Expr expd = c.expand(e);
    if (c.kind(expd) != NodeKind::Add)
        return e;

    std::vector<Expr> terms;
    for (std::size_t i = 0; i < c.childCount(expd); ++i)
        terms.push_back(c.child(expd, i));

    const Expr absT = c.func("abs", t);
    bool changed = true;
    while (changed) {
        changed = false;
        for (std::size_t i = 0; i < terms.size() && !changed; ++i) {
            Expr K;
            if (!stripSignT(terms[i], K))
                continue;
            const Expr negK = c.simplify(c.neg(K));
            for (std::size_t j = 0; j < terms.size() && !changed; ++j) {
                if (i == j)
                    continue;
                if (terms[j] == K) {
                    const Expr kPos = c.subs(K, absT, t);
                    terms[std::min(i, j)] = c.simplify(
                        c.mul({c.number(2), kPos, c.func("heaviside", t)}));
                    terms.erase(terms.begin() +
                                static_cast<std::ptrdiff_t>(std::max(i, j)));
                    changed = true;
                } else if (terms[j] == negK) {
                    const Expr kNeg = c.subs(negK, absT, c.neg(t));
                    terms[std::min(i, j)] = c.simplify(c.mul(
                        {c.number(2), kNeg, c.func("heaviside", c.neg(t))}));
                    terms.erase(terms.begin() +
                                static_cast<std::ptrdiff_t>(std::max(i, j)));
                    changed = true;
                }
            }
        }
    }
    return terms.empty() ? c.zero() : c.simplify(c.add(terms));
}

// Normalize `heaviside(a - abs(w))` into `1/2 * (sign(w + a) - sign(w - a))`
// so round-trip certification matches boxcar/sinc representations identically.
Expr normalizeBoxcarForCert(Ctx &c, Expr e, Expr w)
{
    if (e.isNull())
        return Expr();
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        const Expr arg = normalizeBoxcarForCert(c, c.child(e, 0), w);
        if (c.funcName(e) == "heaviside") {
            const Expr aConst = c.simplify(c.add({arg, c.func("abs", w)}));
            if (!dependsOn(c, aConst, w) && c.isAssumedPositive(aConst)) {
                return c.mul(
                    {c.number(Rational(1, BigInt(2))),
                     c.add({c.func("sign", c.add({w, aConst})),
                            c.neg(c.func("sign",
                                         c.add({w, c.neg(aConst)})))})});
            }
        }
        return c.func(c.funcName(e), arg);
    }
    case NodeKind::Pow:
        return c.pow(normalizeBoxcarForCert(c, c.child(e, 0), w),
                     normalizeBoxcarForCert(c, c.child(e, 1), w));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            ch.push_back(normalizeBoxcarForCert(c, c.child(e, i), w));
        return c.kind(e) == NodeKind::Add ? c.add(ch) : c.mul(ch);
    }
    }
    return e;
}

bool certifyInverseFourier(Ctx &c, Expr fCand, Expr targetF, Expr w, Expr t,
                           Budget *budget)
{
    const FourierResult fwd = fourier(c, fCand, t, w, budget);
    if (!fwd.proved())
        return false;
    const Expr normGot = normalizeBoxcarForCert(c, fwd.F, w);
    const Expr normTarget = normalizeBoxcarForCert(c, targetF, w);
    Expr r1, m1, r2, m2;
    if (!splitComplexI(c, normGot, r1, m1) ||
        !splitComplexI(c, normTarget, r2, m2))
        return false;
    return c.isZero(c.simplify(c.add({r1, c.neg(r2)}))) &&
           c.isZero(c.simplify(c.add({m1, c.neg(m2)})));
}

} // namespace

FourierResult fourier(Ctx &c, Expr f, Expr t, Expr w, Budget *budget)
{
    FourierResult out;
    if (f.isNull() || t.isNull() || w.isNull() ||
        c.kind(t) != NodeKind::Symbol) {
        out.reason = "invalid input arguments";
        return out;
    }
    Expr re, im;
    if (!fourierComplexExpr(c, f, t, w, -1, budget, re, im, out.reason))
        return out;
    if (c.isZero(im)) {
        out.F = re;
    } else if (c.isZero(re)) {
        out.F = c.simplify(c.mul({c.symbol("I"), im}));
    } else {
        out.F = c.simplify(c.add({re, c.mul({c.symbol("I"), im})}));
    }
    out.status = FourierResult::Status::ProvedSymbolic;
    return out;
}

FourierResult ifourier(Ctx &c, Expr F, Expr w, Expr t, Budget *budget)
{
    FourierResult out;
    if (F.isNull() || w.isNull() || t.isNull() ||
        c.kind(w) != NodeKind::Symbol) {
        out.reason = "invalid input arguments";
        return out;
    }

    // Direct causal pole shortcut: C * (a + I*w)^(-n) -> C * t^(n-1)/(n-1)! * exp(-a*t) * heaviside(t)
    {
        std::vector<Expr> facs;
        if (c.kind(F) == NodeKind::Mul) {
            for (std::size_t i = 0; i < c.childCount(F); ++i)
                facs.push_back(c.child(F, i));
        } else {
            facs.push_back(F);
        }
        std::vector<Expr> constFacs;
        Expr poleBase;
        std::int64_t poleOrder = 0;
        bool okPole = true;
        for (const Expr &fac : facs) {
            if (!dependsOn(c, fac, w) && !mentionsSymbolName(c, fac, "I")) {
                constFacs.push_back(fac);
            } else if (poleOrder == 0 && c.kind(fac) == NodeKind::Pow &&
                       c.kind(c.child(fac, 1)) == NodeKind::Number) {
                std::int64_t k = 0;
                if (c.numberValue(c.child(fac, 1)).den() == BigInt(1) &&
                    c.numberValue(c.child(fac, 1)).num().fitsInt64(k) &&
                    k <= -1 && k >= -8) {
                    poleBase = c.child(fac, 0);
                    poleOrder = -k;
                } else {
                    okPole = false;
                    break;
                }
            } else {
                okPole = false;
                break;
            }
        }
        if (okPole && poleOrder >= 1) {
            Expr bRe, bIm;
            if (splitComplexI(c, poleBase, bRe, bIm) && !dependsOn(c, bRe, w) &&
                c.isAssumedPositive(bRe) && bIm == w) {
                BigInt fact(1);
                for (std::int64_t i = 2; i < poleOrder; ++i)
                    fact = fact * BigInt(i);
                const Expr cCoef =
                    constFacs.empty() ? c.one() : c.mul(constFacs);
                const Expr tPow =
                    (poleOrder == 1) ? c.one()
                                     : c.pow(t, c.number(poleOrder - 1));
                const Expr fCand = c.simplify(c.mul(
                    {cCoef, c.number(Rational(BigInt(1), fact)), tPow,
                     c.func("exp", c.neg(c.mul({bRe, t}))),
                     c.func("heaviside", t)}));
                if (certifyInverseFourier(c, fCand, F, w, t, budget)) {
                    out.F = fCand;
                    out.status = FourierResult::Status::ProvedSymbolic;
                    return out;
                }
            }
        }
    }

    Expr re, im;
    if (!fourierComplexExpr(c, F, w, t, +1, budget, re, im, out.reason))
        return out;
    const Expr invTwoPi =
        c.div(c.one(), c.mul({c.number(2), c.symbol("pi")}));
    Expr fCand;
    if (c.isZero(im)) {
        fCand = c.simplify(c.mul({invTwoPi, re}));
    } else if (c.isZero(re)) {
        fCand = c.simplify(c.mul({invTwoPi, c.symbol("I"), im}));
    } else {
        fCand = c.simplify(
            c.mul({invTwoPi, c.add({re, c.mul({c.symbol("I"), im})})}));
    }
    fCand = canonicalizeHeavisideExp(c, fCand, t);

    if (!certifyInverseFourier(c, fCand, F, w, t, budget)) {
        out.reason = "inverse Fourier round-trip certificate failed";
        return out;
    }
    out.F = fCand;
    out.status = FourierResult::Status::ProvedSymbolic;
    return out;
}

} // namespace numkit::cas
