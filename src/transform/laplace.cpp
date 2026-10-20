#include <numkit/cas/transform/laplace.hpp>

#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

#include <cstdint>
#include <vector>

namespace numkit::cas {
namespace {

bool checkLaplaceBudget(const Ctx &c, Budget *budget, std::string &reasonOut)
{
    if (!budget)
        return true;
    if (!budget->step() || !budget->recordArenaBytes(c.nodeCount() * 32)) {
        reasonOut = budget->status() == BudgetStatus::StepExhausted
                        ? "step budget exhausted"
                        : "arena byte budget exhausted";
        return false;
    }
    return true;
}

bool mentionsSymbol(const Ctx &c, Expr e, Expr var)
{
    if (e.isNull())
        return false;
    if (e == var)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        if (mentionsSymbol(c, c.child(e, i), var))
            return true;
    return false;
}

BigInt factorialBigInt(std::int64_t n)
{
    BigInt acc(1);
    for (std::int64_t k = 2; k <= n; ++k)
        acc *= BigInt(k);
    return acc;
}

// Coefficient (2k)! / (4^k * k!) in Gamma(k + 1/2) = coeff * sqrt(pi).
Rational halfIntGammaCoeff(std::int64_t k)
{
    const BigInt num = factorialBigInt(2 * k);
    const BigInt den =
        BigInt::powUInt(BigInt(4), static_cast<std::uint64_t>(k)) *
        factorialBigInt(k);
    return Rational(num, den);
}

// Factor a positive rational v^(exp) into canonical prime-base powers
// prod_i p_i^(k_i * exp) so that e.g. 4^(1/2) -> 2 and 8^(1/2) -> 2*2^(1/2).
Expr factorPosRationalPower(Ctx &c, const Rational &v, const Rational &exp)
{
    if (v == Rational(std::int64_t{1}) || exp.isZero())
        return c.one();
    std::vector<Expr> parts;
    for (const auto &pk : BigInt::factorize(v.num())) {
        parts.push_back(c.pow(
            c.number(Rational(pk.first, BigInt(1))),
            c.number(exp * Rational(static_cast<std::int64_t>(pk.second)))));
    }
    for (const auto &pk : BigInt::factorize(v.den())) {
        parts.push_back(c.pow(
            c.number(Rational(pk.first, BigInt(1))),
            c.number(-exp * Rational(static_cast<std::int64_t>(pk.second)))));
    }
    return parts.empty() ? c.one() : c.mul(parts);
}

// Decompose e = c0 + c1 * var where c0, c1 are free of var.
bool extractLinearInVar(Ctx &c, Expr e, Expr var, Expr &c0Out, Expr &c1Out)
{
    if (!mentionsSymbol(c, e, var)) {
        c0Out = e;
        c1Out = c.zero();
        return true;
    }
    if (e == var) {
        c0Out = c.zero();
        c1Out = c.one();
        return true;
    }
    const Expr ex = c.expand(e);
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
    if (c.kind(ex) == NodeKind::Mul) {
        std::vector<Expr> others;
        int varCount = 0;
        for (std::size_t i = 0; i < c.childCount(ex); ++i) {
            const Expr ch = c.child(ex, i);
            if (ch == var) {
                ++varCount;
            } else if (!mentionsSymbol(c, ch, var)) {
                others.push_back(ch);
            } else {
                return false;
            }
        }
        if (varCount == 1) {
            c0Out = c.zero();
            c1Out = others.empty() ? c.one() : c.mul(others);
            return true;
        }
        return false;
    }
    if (c.kind(ex) == NodeKind::Add) {
        std::vector<Expr> c0Terms;
        std::vector<Expr> c1Terms;
        for (std::size_t i = 0; i < c.childCount(ex); ++i) {
            Expr sub0, sub1;
            if (!extractLinearInVar(c, c.child(ex, i), var, sub0, sub1))
                return false;
            if (!c.isZero(sub0))
                c0Terms.push_back(sub0);
            if (!c.isZero(sub1))
                c1Terms.push_back(sub1);
        }
        c0Out = c0Terms.empty() ? c.zero() : c.add(c0Terms);
        c1Out = c1Terms.empty() ? c.zero() : c.add(c1Terms);
        return true;
    }
    return false;
}

// Decompose e = c0 + c1 * var + c2 * var^2 where c0, c1, c2 are free of var.
bool extractQuadraticInVar(Ctx &c, Expr e, Expr var, Expr &c0Out, Expr &c1Out,
                           Expr &c2Out)
{
    const Expr ex = c.expand(e);
    auto matchMonomial = [&](Expr term, int &degOut, Expr &coeffOut) -> bool {
        if (!mentionsSymbol(c, term, var)) {
            degOut = 0;
            coeffOut = term;
            return true;
        }
        if (term == var) {
            degOut = 1;
            coeffOut = c.one();
            return true;
        }
        if (c.kind(term) == NodeKind::Pow && c.child(term, 0) == var &&
            c.child(term, 1) == c.number(std::int64_t{2})) {
            degOut = 2;
            coeffOut = c.one();
            return true;
        }
        if (c.kind(term) == NodeKind::Mul) {
            std::vector<Expr> others;
            int deg = 0;
            for (std::size_t i = 0; i < c.childCount(term); ++i) {
                const Expr ch = c.child(term, i);
                if (ch == var) {
                    deg += 1;
                } else if (c.kind(ch) == NodeKind::Pow &&
                           c.child(ch, 0) == var &&
                           c.child(ch, 1) == c.number(std::int64_t{2})) {
                    deg += 2;
                } else if (!mentionsSymbol(c, ch, var)) {
                    others.push_back(ch);
                } else {
                    return false;
                }
            }
            if (deg <= 2) {
                degOut = deg;
                coeffOut = others.empty() ? c.one() : c.mul(others);
                return true;
            }
        }
        return false;
    };

    std::vector<Expr> degTerms[3];
    if (c.kind(ex) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(ex); ++i) {
            int d = 0;
            Expr cf;
            if (!matchMonomial(c.child(ex, i), d, cf))
                return false;
            degTerms[d].push_back(cf);
        }
    } else {
        int d = 0;
        Expr cf;
        if (!matchMonomial(ex, d, cf))
            return false;
        degTerms[d].push_back(cf);
    }
    c0Out = degTerms[0].empty() ? c.zero() : c.add(degTerms[0]);
    c1Out = degTerms[1].empty() ? c.zero() : c.add(degTerms[1]);
    c2Out = degTerms[2].empty() ? c.zero() : c.add(degTerms[2]);
    return !c.isZero(c2Out);
}

// Rewrite hyperbolic functions into exponentials:
//   sinh(u) -> 1/2*(exp(u) - exp(-u)), cosh(u) -> 1/2*(exp(u) + exp(-u)).
Expr rewriteHypToExp(Ctx &c, Expr e, Expr var)
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
        const Expr u = rewriteHypToExp(c, c.child(e, 0), var);
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
        return c.pow(rewriteHypToExp(c, c.child(e, 0), var),
                     rewriteHypToExp(c, c.child(e, 1), var));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(rewriteHypToExp(c, c.child(e, i), var));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

// Expand products and positive integer powers of sin/cos into sums of single
// sin/cos calls via product-to-sum identities.
Expr reduceTrigProductsOnce(Ctx &c, Expr e, Expr var, bool &changed)
{
    if (e.isNull() || !mentionsSymbol(c, e, var))
        return e;
    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));

    if (c.kind(e) == NodeKind::Pow && c.kind(c.child(e, 0)) == NodeKind::Func &&
        c.kind(c.child(e, 1)) == NodeKind::Number) {
        const std::string &fn = c.funcName(c.child(e, 0));
        const Expr u = c.child(c.child(e, 0), 0);
        std::int64_t k = 0;
        if ((fn == "sin" || fn == "cos" || fn == "sinh" || fn == "cosh") &&
            c.numberValue(c.child(e, 1)).den() == BigInt(1) &&
            c.numberValue(c.child(e, 1)).num().fitsInt64(k) && k >= 2 &&
            k <= 12) {
            changed = true;
            const Expr twoU = c.mul({c.number(std::int64_t{2}), u});
            Expr sq;
            if (fn == "sin") {
                sq = c.mul({half, c.add({c.one(), c.neg(c.func("cos", twoU))})});
            } else if (fn == "cos") {
                sq = c.mul({half, c.add({c.one(), c.func("cos", twoU)})});
            } else if (fn == "sinh") {
                sq = c.mul(
                    {half, c.add({c.func("cosh", twoU), c.neg(c.one())})});
            } else {
                sq = c.mul({half, c.add({c.func("cosh", twoU), c.one()})});
            }
            if (k == 2)
                return sq;
            return c.mul({sq, c.pow(c.child(e, 0), c.number(k - 2))});
        }
    }

    if (c.kind(e) == NodeKind::Mul) {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(reduceTrigProductsOnce(c, c.child(e, i), var, changed));
        if (changed)
            return c.expand(c.mul(kids));

        int idx1 = -1, idx2 = -1;
        bool hypPair = false;
        for (std::size_t i = 0; i < kids.size(); ++i) {
            if (c.kind(kids[i]) == NodeKind::Func &&
                mentionsSymbol(c, kids[i], var)) {
                const std::string &fn = c.funcName(kids[i]);
                if (fn == "sin" || fn == "cos") {
                    if (idx1 < 0) {
                        idx1 = static_cast<int>(i);
                        hypPair = false;
                    } else if (!hypPair) {
                        idx2 = static_cast<int>(i);
                        break;
                    }
                } else if (fn == "sinh" || fn == "cosh") {
                    if (idx1 < 0) {
                        idx1 = static_cast<int>(i);
                        hypPair = true;
                    } else if (hypPair) {
                        idx2 = static_cast<int>(i);
                        break;
                    }
                }
            }
        }
        if (idx1 >= 0 && idx2 >= 0) {
            changed = true;
            const Expr f1 = kids[static_cast<std::size_t>(idx1)];
            const Expr f2 = kids[static_cast<std::size_t>(idx2)];
            const std::string &fn1 = c.funcName(f1);
            const std::string &fn2 = c.funcName(f2);
            const Expr u = c.child(f1, 0);
            const Expr v = c.child(f2, 0);
            const Expr uPlusV = c.add({u, v});
            const Expr uMinusV = c.add({u, c.neg(v)});
            Expr pairSum;
            if (!hypPair) {
                if (fn1 == "sin" && fn2 == "cos") {
                    pairSum = c.mul({half, c.add({c.func("sin", uPlusV),
                                                  c.func("sin", uMinusV)})});
                } else if (fn1 == "cos" && fn2 == "sin") {
                    pairSum = c.mul(
                        {half, c.add({c.func("sin", uPlusV),
                                      c.neg(c.func("sin", uMinusV))})});
                } else if (fn1 == "sin" && fn2 == "sin") {
                    pairSum = c.mul(
                        {half, c.add({c.func("cos", uMinusV),
                                      c.neg(c.func("cos", uPlusV))})});
                } else {
                    pairSum = c.mul({half, c.add({c.func("cos", uMinusV),
                                                  c.func("cos", uPlusV)})});
                }
            } else {
                if (fn1 == "sinh" && fn2 == "cosh") {
                    pairSum = c.mul({half, c.add({c.func("sinh", uPlusV),
                                                  c.func("sinh", uMinusV)})});
                } else if (fn1 == "cosh" && fn2 == "sinh") {
                    pairSum = c.mul(
                        {half, c.add({c.func("sinh", uPlusV),
                                      c.neg(c.func("sinh", uMinusV))})});
                } else if (fn1 == "sinh" && fn2 == "sinh") {
                    pairSum = c.mul(
                        {half, c.add({c.func("cosh", uPlusV),
                                      c.neg(c.func("cosh", uMinusV))})});
                } else {
                    pairSum = c.mul({half, c.add({c.func("cosh", uPlusV),
                                                  c.func("cosh", uMinusV)})});
                }
            }
            std::vector<Expr> rest;
            rest.push_back(pairSum);
            for (std::size_t i = 0; i < kids.size(); ++i) {
                if (static_cast<int>(i) != idx1 && static_cast<int>(i) != idx2)
                    rest.push_back(kids[i]);
            }
            return c.expand(c.mul(rest));
        }
        return c.mul(kids);
    }

    if (c.kind(e) == NodeKind::Add) {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(reduceTrigProductsOnce(c, c.child(e, i), var, changed));
        return c.add(kids);
    }
    return e;
}

LaplaceResult laplaceRec(Ctx &c, Expr f, Expr t, Expr s, Budget *budget,
                         int depth)
{
    LaplaceResult out;
    if (!checkLaplaceBudget(c, budget, out.reason))
        return out;
    if (depth > 8) {
        out.reason = "maximum Laplace recursion depth exceeded";
        return out;
    }

    if (c.isZero(f)) {
        out.status = LaplaceResult::Status::ProvedSymbolic;
        out.F = c.zero();
        return out;
    }

    // 1. Constant (free of t): L{C}(s) = C / s.
    if (!mentionsSymbol(c, f, t)) {
        out.status = LaplaceResult::Status::ProvedSymbolic;
        out.F = c.div(f, s);
        return out;
    }

    // 2. Linearity over Add: L{sum f_i}(s) = sum L{f_i}(s).
    if (c.kind(f) == NodeKind::Add) {
        std::vector<Expr> parts;
        parts.reserve(c.childCount(f));
        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            const LaplaceResult ri =
                laplaceRec(c, c.child(f, i), t, s, budget, depth + 1);
            if (!ri.proved())
                return ri;
            parts.push_back(ri.F);
        }
        out.status = LaplaceResult::Status::ProvedSymbolic;
        out.F = c.add(parts);
        return out;
    }

    // 3. Direct variable t: L{t}(s) = 1 / s^2.
    if (f == t) {
        out.status = LaplaceResult::Status::ProvedSymbolic;
        out.F = c.pow(s, c.number(std::int64_t{-2}));
        return out;
    }

    // 4. Power of t: t^n (integer n >= 0) or t^(k - 1/2) (half-integer k >= 0).
    if (c.kind(f) == NodeKind::Pow && c.child(f, 0) == t &&
        c.kind(c.child(f, 1)) == NodeKind::Number) {
        const Rational &re = c.numberValue(c.child(f, 1));
        std::int64_t n = 0;
        if (re.den() == BigInt(1) && re.num().fitsInt64(n) && n >= 0 &&
            n <= 64) {
            out.status = LaplaceResult::Status::ProvedSymbolic;
            out.F = c.mul({c.number(Rational(factorialBigInt(n), BigInt(1))),
                           c.pow(s, c.number(-(n + 1)))});
            return out;
        }
        std::int64_t num2 = 0;
        if (re.den() == BigInt(2) && re.num().fitsInt64(num2) && num2 >= -1 &&
            num2 <= 63) {
            // re = (2*k - 1)/2 -> k = (num2 + 1)/2 >= 0
            const std::int64_t k = (num2 + 1) / 2;
            const Rational coeff = halfIntGammaCoeff(k);
            const Expr sqrtPi = c.pow(
                c.symbol("pi"), c.number(Rational(std::int64_t{1}, BigInt(2))));
            out.status = LaplaceResult::Status::ProvedSymbolic;
            out.F = c.mul({c.number(coeff), sqrtPi,
                           c.pow(s, c.number(Rational(-(2 * k + 1), BigInt(2))))});
            return out;
        }
    }

    // 5. Elementary Func of linear argument phi + w*t: exp, sin, cos, sinh, cosh, sqrt.
    if (c.kind(f) == NodeKind::Func) {
        const std::string &fn = c.funcName(f);
        const Expr arg = c.child(f, 0);
        if (fn == "sqrt") {
            return laplaceRec(
                c,
                c.pow(arg, c.number(Rational(std::int64_t{1}, BigInt(2)))), t,
                s, budget, depth + 1);
        }
        Expr phi, w;
        if (extractLinearInVar(c, arg, t, phi, w) && !c.isZero(w)) {
            const Expr s2 = c.pow(s, c.number(std::int64_t{2}));
            const Expr w2 = c.pow(w, c.number(std::int64_t{2}));
            if (fn == "exp") {
                const Expr shiftDen = c.add({s, c.neg(w)});
                const Expr pref =
                    c.isZero(phi) ? c.one() : c.func("exp", phi);
                out.status = LaplaceResult::Status::ProvedSymbolic;
                out.F = c.div(pref, shiftDen);
                return out;
            }
            if (fn == "sin") {
                const Expr den = c.add({s2, w2});
                const Expr num =
                    c.isZero(phi)
                        ? w
                        : c.add({c.mul({c.func("sin", phi), s}),
                                 c.mul({c.func("cos", phi), w})});
                out.status = LaplaceResult::Status::ProvedSymbolic;
                out.F = c.div(num, den);
                return out;
            }
            if (fn == "cos") {
                const Expr den = c.add({s2, w2});
                const Expr num =
                    c.isZero(phi)
                        ? s
                        : c.add({c.mul({c.func("cos", phi), s}),
                                 c.neg(c.mul({c.func("sin", phi), w}))});
                out.status = LaplaceResult::Status::ProvedSymbolic;
                out.F = c.div(num, den);
                return out;
            }
            if (fn == "sinh") {
                const Expr den = c.add({s2, c.neg(w2)});
                const Expr num =
                    c.isZero(phi)
                        ? w
                        : c.add({c.mul({c.func("sinh", phi), s}),
                                 c.mul({c.func("cosh", phi), w})});
                out.status = LaplaceResult::Status::ProvedSymbolic;
                out.F = c.div(num, den);
                return out;
            }
            if (fn == "cosh") {
                const Expr den = c.add({s2, c.neg(w2)});
                const Expr num =
                    c.isZero(phi)
                        ? s
                        : c.add({c.mul({c.func("cosh", phi), s}),
                                 c.mul({c.func("sinh", phi), w})});
                out.status = LaplaceResult::Status::ProvedSymbolic;
                out.F = c.div(num, den);
                return out;
            }
        }
    }

    // 6. Product rules in Mul:
    //    - Factor out t-free constants: L{C * g(t)} = C * L{g(t)}(s)
    //    - First shifting theorem: L{exp(phi + a*t) * g(t)}(s) = exp(phi) * G(s - a)
    //    - Frequency differentiation: L{t^n * g(t)}(s) = (-1)^n d^n/ds^n G(s)
    if (c.kind(f) == NodeKind::Mul) {
        std::vector<Expr> constFactors;
        std::vector<Expr> expPhis;
        std::vector<Expr> expShifts;
        std::int64_t tPow = 0;
        std::vector<Expr> otherFactors;

        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            const Expr ch = c.child(f, i);
            if (!mentionsSymbol(c, ch, t)) {
                constFactors.push_back(ch);
                continue;
            }
            if (ch == t) {
                tPow += 1;
                continue;
            }
            if (c.kind(ch) == NodeKind::Pow && c.child(ch, 0) == t &&
                c.kind(c.child(ch, 1)) == NodeKind::Number) {
                const Rational &re = c.numberValue(c.child(ch, 1));
                std::int64_t k = 0;
                if (re.den() == BigInt(1) && re.num().fitsInt64(k) && k >= 1 &&
                    k <= 16) {
                    tPow += k;
                    continue;
                }
            }
            if (c.kind(ch) == NodeKind::Func && c.funcName(ch) == "exp") {
                Expr phi, a;
                if (extractLinearInVar(c, c.child(ch, 0), t, phi, a)) {
                    if (!c.isZero(phi))
                        expPhis.push_back(phi);
                    if (!c.isZero(a))
                        expShifts.push_back(a);
                    continue;
                }
            }
            otherFactors.push_back(ch);
        }

        if (!expPhis.empty()) {
            constFactors.push_back(c.func("exp", c.add(expPhis)));
        }

        if (!constFactors.empty() || !expShifts.empty() ||
            (tPow > 0 && !otherFactors.empty()) ||
            (tPow > 0 && otherFactors.empty() && !expShifts.empty())) {
            const Expr coreT =
                otherFactors.empty()
                    ? (tPow > 0 ? c.pow(t, c.number(tPow)) : c.one())
                    : (otherFactors.size() == 1 ? otherFactors[0]
                                                : c.mul(otherFactors));
            const bool applyDiffAfter = (tPow > 0 && !otherFactors.empty());

            const LaplaceResult coreRes =
                laplaceRec(c, coreT, t, s, budget, depth + 1);
            if (coreRes.proved()) {
                Expr G = coreRes.F;
                if (applyDiffAfter) {
                    for (std::int64_t k = 0; k < tPow; ++k)
                        G = c.diff(G, s);
                    if (tPow % 2 != 0)
                        G = c.neg(G);
                }
                if (!expShifts.empty()) {
                    const Expr totalShift = c.add(expShifts);
                    G = c.subs(G, s, c.add({s, c.neg(totalShift)}));
                }
                if (!constFactors.empty()) {
                    constFactors.push_back(G);
                    G = c.mul(constFactors);
                }
                out.status = LaplaceResult::Status::ProvedSymbolic;
                out.F = G;
                return out;
            }
        }
    }

    // 7. Expand polynomial/exponential products or powers (e.g. (t + 1)^2, sinh^2(t)).
    const Expr expanded = c.expand(f);
    if (expanded != f) {
        const LaplaceResult rExp =
            laplaceRec(c, expanded, t, s, budget, depth + 1);
        if (rExp.proved())
            return rExp;
    }

    // 8. Reduce products/powers of sin/cos via product-to-sum identities, and
    //    rewrite remaining hyperbolic products/powers into exponentials.
    bool trigChanged = false;
    Expr trigReduced = expanded;
    for (int pass = 0; pass < 6; ++pass) {
        bool stepChanged = false;
        trigReduced = reduceTrigProductsOnce(c, trigReduced, t, stepChanged);
        if (!stepChanged)
            break;
        trigChanged = true;
    }
    if (trigChanged) {
        const LaplaceResult rTrig =
            laplaceRec(c, trigReduced, t, s, budget, depth + 1);
        if (rTrig.proved())
            return rTrig;
    }

    const Expr hypExp = c.expand(rewriteHypToExp(c, trigReduced, t));
    if (hypExp != trigReduced) {
        const LaplaceResult rHyp =
            laplaceRec(c, hypExp, t, s, budget, depth + 1);
        if (rHyp.proved())
            return rHyp;
    }

    out.reason = "outside elementary Laplace transform domain";
    return out;
}

// Invert a single partial fraction term R(s) / P(s)^j over Q[s], where
// deg(R) < deg(P) and P is monic irreducible of degree 1 or 2.
bool invertPartialFractionTerm(Ctx &c, const UPoly &R, const UPoly &P, int j,
                               Expr t, Expr &outTerm)
{
    if (R.isZero()) {
        outTerm = c.zero();
        return true;
    }
    if (P.deg() == 1) {
        // P(s) = s + p0 => pole at r = -p0.
        // L^{-1}{c0 / (s - r)^j} = c0 * t^(j-1) / (j-1)! * exp(r*t).
        const Rational c0 = R.coeff(0);
        const Rational r = -P.coeff(0);
        const Rational coef = c0 / Rational(factorialBigInt(j - 1), BigInt(1));
        std::vector<Expr> factors;
        factors.push_back(c.number(coef));
        if (j > 1)
            factors.push_back(c.pow(t, c.number(static_cast<std::int64_t>(j - 1))));
        if (!r.isZero())
            factors.push_back(c.func("exp", c.mul({c.number(r), t})));
        outTerm = c.mul(factors);
        return true;
    }
    if (P.deg() == 2 && (j == 1 || j == 2)) {
        // P(s) = s^2 + b*s + c0 = (s - alpha)^2 + Delta
        const Rational b = P.coeff(1);
        const Rational c0 = P.coeff(0);
        const Rational alpha = -b / Rational(std::int64_t{2});
        const Rational delta = c0 - (b * b) / Rational(std::int64_t{4});
        if (delta.isZero())
            return false;

        // R(s) = beta1 * s + beta0 = A * (s - alpha) + B
        const Rational beta1 = R.coeff(1);
        const Rational beta0 = R.coeff(0);
        const Rational A = beta1;
        const Rational B = beta0 + beta1 * alpha;

        const bool isOscillatory = delta.signum() > 0;
        const Rational absDelta = isOscillatory ? delta : -delta;
        const Expr w = factorPosRationalPower(
            c, absDelta, Rational(std::int64_t{1}, BigInt(2)));
        const Expr invW = factorPosRationalPower(
            c, absDelta, Rational(std::int64_t{-1}, BigInt(2)));
        const Expr invW3 = factorPosRationalPower(
            c, absDelta, Rational(std::int64_t{-3}, BigInt(2)));
        const Expr wt = c.mul({w, t});
        const Expr cosFn = isOscillatory ? c.func("cos", wt) : c.func("cosh", wt);
        const Expr sinFn = isOscillatory ? c.func("sin", wt) : c.func("sinh", wt);
        const Expr expFactor =
            alpha.isZero() ? c.one()
                           : c.func("exp", c.mul({c.number(alpha), t}));

        if (j == 1) {
            std::vector<Expr> pieces;
            if (!A.isZero())
                pieces.push_back(c.mul({c.number(A), cosFn}));
            if (!B.isZero())
                pieces.push_back(c.mul({c.number(B), invW, sinFn}));
            const Expr body = pieces.empty() ? c.zero() : c.add(pieces);
            outTerm = c.mul({expFactor, body});
            return true;
        }
        // j == 2:
        //   L^{-1}{(s - alpha)/((s - alpha)^2 + w^2)^2} = 1/(2*w) * t * e^(alpha*t) * sin(w*t)
        //   L^{-1}{1/((s - alpha)^2 + w^2)^2} = 1/(2*w^3) * e^(alpha*t) * (sin(w*t) - w*t*cos(w*t))
        //   L^{-1}{1/((s - alpha)^2 - w^2)^2} = 1/(2*w^3) * e^(alpha*t) * (w*t*cosh(w*t) - sinh(w*t))
        std::vector<Expr> pieces;
        if (!A.isZero()) {
            pieces.push_back(c.mul(
                {c.number(A / Rational(std::int64_t{2})), invW, t, sinFn}));
        }
        if (!B.isZero()) {
            const Expr inner =
                isOscillatory
                    ? c.add({sinFn, c.neg(c.mul({w, t, cosFn}))})
                    : c.add({c.mul({w, t, cosFn}), c.neg(sinFn)});
            pieces.push_back(c.mul(
                {c.number(B / Rational(std::int64_t{2})), invW3, inner}));
        }
        const Expr body = pieces.empty() ? c.zero() : c.add(pieces);
        outTerm = c.mul({expFactor, body});
        return true;
    }
    return false;
}

bool tryRationalIlaplace(Ctx &c, Expr F, Expr s, Expr t, Budget *budget,
                         Expr &outF, std::string &reasonOut)
{
    UPoly N, D;
    if (!toRational(c, F, s, N, D))
        return false;
    if (D.isZero())
        return false;
    if (N.isZero()) {
        outF = c.zero();
        return true;
    }
    if (D.isConst() || N.deg() >= D.deg()) {
        reasonOut =
            "rational function is not strictly proper (deg(N) >= deg(D))";
        return false;
    }

    // Normalize D to monic and divide N by lc(D).
    const Rational lcD = D.lc();
    N = N * UPoly(Rational(std::int64_t{1}) / lcD);
    D.makeMonic();

    const std::vector<UPoly> rawFactors = factorOverQ(D, budget);
    if (budget && !budget->ok()) {
        reasonOut = budget->status() == BudgetStatus::StepExhausted
                        ? "step budget exhausted"
                        : "arena byte budget exhausted";
        return false;
    }
    if (rawFactors.empty())
        return false;

    std::vector<std::pair<UPoly, std::uint64_t>> grouped;
    for (UPoly f : rawFactors) {
        f.makeMonic();
        bool found = false;
        for (auto &kv : grouped) {
            if (kv.first == f) {
                ++kv.second;
                found = true;
                break;
            }
        }
        if (!found)
            grouped.push_back({f, 1});
    }

    // Coprime partial fraction decomposition N / prod_i P_i^{m_i} = sum_i A_i / P_i^{m_i}
    std::vector<UPoly> primePowers;
    primePowers.reserve(grouped.size());
    for (const auto &fe : grouped)
        primePowers.push_back(fe.first.powUInt(fe.second));

    std::vector<UPoly> numerators(grouped.size());
    UPoly remNum = N;
    UPoly remDen = D;
    for (std::size_t i = 0; i < grouped.size(); ++i) {
        const UPoly &PiM = primePowers[i];
        if (i + 1 == grouped.size()) {
            numerators[i] = remNum;
            break;
        }
        UPoly Q, rDiv;
        UPoly::divMod(remDen, PiM, Q, rDiv);
        // v * Q == 1 (mod PiM) since gcd(PiM, Q) = 1
        const UPoly v = UPoly::invMod(Q, PiM);
        const UPoly Ai = (remNum * v) % PiM;
        numerators[i] = Ai;
        UPoly nextNum, remZero;
        UPoly::divMod(remNum - Ai * Q, PiM, nextNum, remZero);
        remNum = nextNum;
        remDen = Q;
    }

    // P_i-adic expansion of each A_i / P_i^{m_i} = sum_{j=1}^{m_i} R_{i,j} / P_i^j
    std::vector<Expr> timeTerms;
    for (std::size_t i = 0; i < grouped.size(); ++i) {
        const UPoly &P = grouped[i].first;
        const int m = static_cast<int>(grouped[i].second);
        UPoly cur = numerators[i];
        for (int j = m; j >= 1; --j) {
            UPoly q, rem;
            UPoly::divMod(cur, P, q, rem);
            if (!rem.isZero()) {
                Expr piece;
                if (!invertPartialFractionTerm(c, rem, P, j, t, piece)) {
                    reasonOut =
                        "irreducible denominator factor of degree > 2 in ilaplace";
                    return false;
                }
                timeTerms.push_back(piece);
            }
            cur = q;
        }
    }

    outF = timeTerms.empty() ? c.zero() : c.add(timeTerms);
    return true;
}

// Parametric symbolic inverse Laplace for terms with symbolic parameters
// (e.g. 1/(s - a)^n, w/(s^2 + w^2), (s + a)/((s + a)^2 + w^2), s^(-k - 1/2)).
bool tryParametricIlaplace(Ctx &c, Expr F, Expr s, Expr t, Budget *budget,
                           Expr &outF)
{
    if (budget && !budget->ok())
        return false;
    if (c.isZero(F)) {
        outF = c.zero();
        return true;
    }

    // 1. Linearity over Add
    if (c.kind(F) == NodeKind::Add) {
        std::vector<Expr> pieces;
        pieces.reserve(c.childCount(F));
        for (std::size_t i = 0; i < c.childCount(F); ++i) {
            Expr pi;
            if (!tryParametricIlaplace(c, c.child(F, i), s, t, budget, pi))
                return false;
            pieces.push_back(pi);
        }
        outF = c.add(pieces);
        return true;
    }

    // 2. Half-integer power of linear (s - a): (c0 + c1*s)^(-(2*k + 1)/2)
    if (c.kind(F) == NodeKind::Pow &&
        c.kind(c.child(F, 1)) == NodeKind::Number) {
        const Rational &re = c.numberValue(c.child(F, 1));
        std::int64_t num2 = 0;
        if (re.den() == BigInt(2) && re.num().fitsInt64(num2) && num2 <= -1 &&
            (-num2) % 2 == 1) {
            const std::int64_t k = (-num2 - 1) / 2;
            Expr c0, c1;
            if (extractLinearInVar(c, c.child(F, 0), s, c0, c1) &&
                c1 == c.one()) {
                const Rational gammaCoeff = halfIntGammaCoeff(k);
                const Rational invCoeff = Rational(std::int64_t{1}) / gammaCoeff;
                const Expr invSqrtPi = c.pow(
                    c.symbol("pi"),
                    c.number(Rational(std::int64_t{-1}, BigInt(2))));
                const Expr tPow = c.pow(
                    t, c.number(Rational(2 * k - 1, BigInt(2))));
                const Expr expShift =
                    c.isZero(c0) ? c.one()
                                 : c.func("exp", c.mul({c.neg(c0), t}));
                outF = c.mul({c.number(invCoeff), invSqrtPi, expShift, tPow});
                return true;
            }
        }
    }

    // 3. Separate s-free constant factors, numerator linear in s, and a single
    //    denominator power D(s)^(-m).
    std::vector<Expr> constFactors;
    std::vector<Expr> sNumFactors;
    Expr denBase;
    std::int64_t denMult = 0;

    auto inspectFactor = [&](Expr ch) -> bool {
        if (!mentionsSymbol(c, ch, s)) {
            constFactors.push_back(ch);
            return true;
        }
        if (c.kind(ch) == NodeKind::Pow &&
            c.kind(c.child(ch, 1)) == NodeKind::Number &&
            c.numberValue(c.child(ch, 1)).signum() < 0) {
            const Rational &re = c.numberValue(c.child(ch, 1));
            std::int64_t m = 0;
            if (re.den() == BigInt(1) && (-re.num()).fitsInt64(m) && m >= 1 &&
                m <= 32) {
                if (!denBase.isNull())
                    return false; // multiple distinct denominator factors
                denBase = c.child(ch, 0);
                denMult = m;
                return true;
            }
            // Also allow single half-integer power factor with s-free cofactors
            if (sNumFactors.empty() && denBase.isNull()) {
                denBase = ch;
                denMult = -1;
                return true;
            }
            return false;
        }
        sNumFactors.push_back(ch);
        return true;
    };

    if (c.kind(F) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(F); ++i) {
            if (!inspectFactor(c.child(F, i)))
                return false;
        }
    } else {
        if (!inspectFactor(F))
            return false;
    }

    if (denMult == -1 && sNumFactors.empty() && !constFactors.empty()) {
        Expr core;
        if (!tryParametricIlaplace(c, denBase, s, t, budget, core))
            return false;
        constFactors.push_back(core);
        outF = c.mul(constFactors);
        return true;
    }

    if (denBase.isNull() || denMult < 1)
        return false;

    const Expr numExpr =
        sNumFactors.empty() ? c.one() : c.mul(sNumFactors);
    Expr beta0, beta1;
    if (!extractLinearInVar(c, numExpr, s, beta0, beta1))
        return false;

    // 3a. Linear denominator denBase = d0 + d1 * s
    Expr d0, d1;
    if (extractLinearInVar(c, denBase, s, d0, d1) && !c.isZero(d1)) {
        if (!c.isZero(beta1))
            return false; // not strictly proper if m == 1
        // denBase^m = d1^m * (s + d0/d1)^m, pole at r = -d0/d1
        const Expr r = c.neg(c.div(d0, d1));
        const Expr scale = c.div(
            beta0,
            c.mul({c.pow(d1, c.number(denMult)),
                   c.number(Rational(factorialBigInt(denMult - 1), BigInt(1)))}));
        std::vector<Expr> parts = constFactors;
        parts.push_back(scale);
        if (denMult > 1)
            parts.push_back(c.pow(t, c.number(denMult - 1)));
        if (!c.isZero(r))
            parts.push_back(c.func("exp", c.mul({r, t})));
        outF = c.mul(parts);
        return true;
    }

    // 3b. Quadratic denominator denBase = q0 + q1 * s + q2 * s^2 (denMult == 1)
    if (denMult == 1) {
        Expr q0, q1, q2;
        if (extractQuadraticInVar(c, denBase, s, q0, q1, q2) &&
            !c.isZero(q2)) {
            const Expr twoQ2 = c.mul({c.number(std::int64_t{2}), q2});
            const Expr alpha = c.simplify(c.neg(c.div(q1, twoQ2)));
            // (s - alpha)^2 + Delta where Delta = q0/q2 - alpha^2
            const Expr delta = c.simplify(
                c.add({c.div(q0, q2),
                       c.neg(c.pow(alpha, c.number(std::int64_t{2})))}));
            if (c.isZero(delta)) {
                // Repeated linear pole (s - alpha)^2:
                // (beta1*(s - alpha) + (beta0 + beta1*alpha)) / (q2 * (s - alpha)^2)
                const Expr A = c.div(beta1, q2);
                const Expr B =
                    c.div(c.add({beta0, c.mul({beta1, alpha})}), q2);
                const Expr expFactor =
                    c.isZero(alpha) ? c.one()
                                    : c.func("exp", c.mul({alpha, t}));
                const Expr body = c.add({A, c.mul({B, t})});
                std::vector<Expr> parts = constFactors;
                parts.push_back(expFactor);
                parts.push_back(body);
                outF = c.mul(parts);
                return true;
            }

            // Decide oscillatory vs hyperbolic branch:
            // If -delta is assumed positive (or delta is a negative constant/product
            // like -w^2), use cosh/sinh with w = sqrt(-delta); otherwise use cos/sin
            // with w = sqrt(delta).
            const Expr negDelta = c.simplify(c.neg(delta));
            bool isHyp = c.isAssumedPositive(negDelta) ||
                         c.isAssumedNegative(delta);
            if (!isHyp && c.kind(delta) == NodeKind::Mul &&
                c.kind(c.child(delta, 0)) == NodeKind::Number &&
                c.numberValue(c.child(delta, 0)).signum() < 0) {
                isHyp = true;
            }
            const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
            const Expr wSq = isHyp ? negDelta : delta;
            Expr w = c.simplify(c.pow(wSq, half));
            // Even when wSq = w0^2 for an unconstrained symbol w0, (w0^2)^(1/2)
            // in Laplace denominator s^2 + w0^2 corresponds to frequency w0:
            if (c.kind(wSq) == NodeKind::Pow &&
                c.child(wSq, 1) == c.number(std::int64_t{2})) {
                w = c.child(wSq, 0);
            }

            const Expr A = c.div(beta1, q2);
            const Expr B = c.div(c.add({beta0, c.mul({beta1, alpha})}), q2);
            const Expr wt = c.mul({w, t});
            const Expr cosFn = isHyp ? c.func("cosh", wt) : c.func("cos", wt);
            const Expr sinFn = isHyp ? c.func("sinh", wt) : c.func("sin", wt);
            const Expr expFactor =
                c.isZero(alpha) ? c.one()
                                : c.func("exp", c.mul({alpha, t}));
            std::vector<Expr> terms;
            if (!c.isZero(A))
                terms.push_back(c.mul({A, cosFn}));
            if (!c.isZero(B))
                terms.push_back(c.mul({c.div(B, w), sinFn}));
            const Expr body = terms.empty() ? c.zero() : c.add(terms);
            std::vector<Expr> parts = constFactors;
            parts.push_back(expFactor);
            parts.push_back(body);
            outF = c.mul(parts);
            return true;
        }
    }

    return false;
}

bool verifyIlaplaceRoundTrip(Ctx &c, Expr fCand, Expr origF, Expr s, Expr t,
                             Budget *budget)
{
    const LaplaceResult fwd = laplace(c, fCand, t, s, budget);
    if (!fwd.proved())
        return false;
    const Expr diff = c.add({fwd.F, c.neg(origF)});
    if (c.isZero(diff))
        return true;
    if (c.isZero(simplifyRationalExpr(c, diff)))
        return true;
    const Expr simpDiff = c.simplify(diff);
    if (c.isZero(simpDiff))
        return true;
    return c.isZero(simplifyRationalExpr(c, simpDiff));
}

} // namespace

LaplaceResult laplace(Ctx &c, Expr f, Expr t, Expr s, Budget *budget)
{
    LaplaceResult out;
    if (f.isNull() || t.isNull() || s.isNull() ||
        c.kind(t) != NodeKind::Symbol || c.kind(s) != NodeKind::Symbol) {
        out.reason = "invalid arguments to laplace";
        return out;
    }
    out = laplaceRec(c, f, t, s, budget, 0);
    if (out.proved())
        out.F = c.simplify(out.F);
    return out;
}

LaplaceResult ilaplace(Ctx &c, Expr F, Expr s, Expr t, Budget *budget)
{
    LaplaceResult out;
    if (F.isNull() || s.isNull() || t.isNull() ||
        c.kind(s) != NodeKind::Symbol || c.kind(t) != NodeKind::Symbol) {
        out.reason = "invalid arguments to ilaplace";
        return out;
    }
    if (!checkLaplaceBudget(c, budget, out.reason))
        return out;

    // 1. Exact rational partial fraction path over Q(s).
    Expr cand;
    std::string ratReason;
    if (tryRationalIlaplace(c, F, s, t, budget, cand, ratReason)) {
        if (verifyIlaplaceRoundTrip(c, cand, F, s, t, budget)) {
            out.status = LaplaceResult::Status::ProvedSymbolic;
            out.F = c.simplify(cand);
            return out;
        }
    } else if (!ratReason.empty()) {
        out.reason = ratReason;
        return out;
    }

    // 2. Parametric symbolic path (and simplified/expanded form).
    for (Expr form : {F, c.simplify(F), simplifyRationalExpr(c, F)}) {
        if (tryParametricIlaplace(c, form, s, t, budget, cand)) {
            if (verifyIlaplaceRoundTrip(c, cand, F, s, t, budget)) {
                out.status = LaplaceResult::Status::ProvedSymbolic;
                out.F = c.simplify(cand);
                return out;
            }
        }
    }

    out.reason = "outside elementary inverse Laplace transform domain";
    return out;
}

} // namespace numkit::cas
