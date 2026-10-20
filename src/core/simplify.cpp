#include <numkit/cas/core/simplify.hpp>

#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

namespace numkit::cas {

namespace {

bool checkSimplifyBudget(const Ctx &c, Budget *budget)
{
    if (!budget)
        return true;
    return budget->step() && budget->recordArenaBytes(c.nodeCount() * 32);
}

// Compare two valid non-null candidates by (exprCost, leafCount).
Expr pickBest(const Ctx &c, Expr a, Expr b)
{
    if (a.isNull())
        return b;
    if (b.isNull())
        return a;
    if (a == b)
        return a;
    const std::size_t costA = c.exprCost(a);
    const std::size_t costB = c.exprCost(b);
    if (costB < costA)
        return b;
    if (costA < costB)
        return a;
    const std::size_t leafA = c.leafCount(a);
    const std::size_t leafB = c.leafCount(b);
    if (leafB < leafA)
        return b;
    return a;
}

// Check if `e` has a negative leading coefficient (`-u` or `-k*u` with k > 0),
// returning `true` and setting `posOut = -e` if so.
bool extractNegativeArg(Ctx &c, Expr e, Expr &posOut)
{
    if (e.isNull())
        return false;
    if (c.kind(e) == NodeKind::Number && c.numberValue(e).signum() < 0) {
        posOut = c.neg(e);
        return true;
    }
    if (c.kind(e) == NodeKind::Mul && c.childCount(e) >= 2 &&
        c.kind(c.child(e, 0)) == NodeKind::Number &&
        c.numberValue(c.child(e, 0)).signum() < 0) {
        posOut = c.neg(e);
        return true;
    }
    return false;
}

enum class SqTrigKind
{
    None,
    Sin2,
    Cos2,
    Sinh2,
    Cosh2,
};

struct SqTrigTerm
{
    SqTrigKind kind = SqTrigKind::None;
    Expr arg;
    Expr cofactor;
    bool exactSq = false;
};

// Check whether a single factor `f` is sin(u)^k, cos(u)^k, sinh(u)^k, or cosh(u)^k
// with integer k >= 2, splitting off fn(u)^2 and returning fn(u)^(k-2) as residual.
bool matchSqTrigFactor(Ctx &c, Expr f, SqTrigKind &kindOut, Expr &argOut,
                       Expr &residualOut, bool &exactSqOut)
{
    if (c.kind(f) != NodeKind::Pow)
        return false;
    const Expr base = c.child(f, 0);
    const Expr exp = c.child(f, 1);
    if (c.kind(base) != NodeKind::Func || c.kind(exp) != NodeKind::Number)
        return false;
    const Rational &re = c.numberValue(exp);
    std::int64_t k = 0;
    if (!(re.den() == BigInt(1)) || !re.num().fitsInt64(k) || k < 2)
        return false;

    const std::string &fn = c.funcName(base);
    if (fn == "sin") {
        kindOut = SqTrigKind::Sin2;
    } else if (fn == "cos") {
        kindOut = SqTrigKind::Cos2;
    } else if (fn == "sinh") {
        kindOut = SqTrigKind::Sinh2;
    } else if (fn == "cosh") {
        kindOut = SqTrigKind::Cosh2;
    } else {
        return false;
    }
    argOut = c.child(base, 0);
    exactSqOut = (k == 2);
    residualOut = (k == 2) ? c.one() : c.pow(base, c.number(k - 2));
    return true;
}

std::vector<SqTrigTerm> analyzeSqTrigTerm(Ctx &c, Expr term)
{
    std::vector<SqTrigTerm> out;
    SqTrigKind k = SqTrigKind::None;
    Expr u;
    Expr residual;
    bool exactSq = false;
    if (matchSqTrigFactor(c, term, k, u, residual, exactSq)) {
        out.push_back(SqTrigTerm{k, u, residual, exactSq});
        return out;
    }
    if (c.kind(term) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(term); ++i) {
            if (matchSqTrigFactor(c, c.child(term, i), k, u, residual, exactSq)) {
                std::vector<Expr> rest;
                if (residual != c.one())
                    rest.push_back(residual);
                for (std::size_t j = 0; j < c.childCount(term); ++j)
                    if (j != i)
                        rest.push_back(c.child(term, j));
                const Expr cof = rest.empty() ? c.one() : c.mul(rest);
                out.push_back(SqTrigTerm{k, u, cof, exactSq});
            }
        }
    }
    return out;
}

// Simplify an Add node using Pythagorean, hyperbolic, and logarithmic rules.
Expr simplifyAddNode(Ctx &c, Expr e)
{
    if (c.kind(e) != NodeKind::Add)
        return e;

    std::vector<Expr> terms;
    terms.reserve(c.childCount(e));
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        terms.push_back(c.child(e, i));

    bool changed = true;
    while (changed) {
        changed = false;
        const std::size_t n = terms.size();
        std::vector<std::vector<SqTrigTerm>> info(n);
        for (std::size_t i = 0; i < n; ++i)
            info[i] = analyzeSqTrigTerm(c, terms[i]);

        // 1a. Exact Pythagorean identity: A*sin(u)^2 + A*cos(u)^2 -> A and
        //     B*cosh(u)^2 - B*sinh(u)^2 -> B (works for any cofactor A, including trig powers).
        for (std::size_t i = 0; i < n && !changed; ++i) {
            for (const SqTrigTerm &ti : info[i]) {
                for (std::size_t j = i + 1; j < n && !changed; ++j) {
                    for (const SqTrigTerm &tj : info[j]) {
                        if (!(ti.arg == tj.arg))
                            continue;
                        const SqTrigTerm *pA = &ti;
                        const SqTrigTerm *pB = &tj;
                        if ((ti.kind == SqTrigKind::Cos2 &&
                             tj.kind == SqTrigKind::Sin2) ||
                            (ti.kind == SqTrigKind::Cosh2 &&
                             tj.kind == SqTrigKind::Sinh2)) {
                            std::swap(pA, pB);
                        }
                        if (pA->kind == SqTrigKind::Sin2 &&
                            pB->kind == SqTrigKind::Cos2 &&
                            pA->cofactor == pB->cofactor) {
                            terms[i] = pA->cofactor;
                            terms.erase(terms.begin() +
                                        static_cast<std::ptrdiff_t>(j));
                            changed = true;
                            break;
                        }
                        if (pA->kind == SqTrigKind::Sinh2 &&
                            pB->kind == SqTrigKind::Cosh2 &&
                            pA->cofactor == c.neg(pB->cofactor)) {
                            terms[i] = pB->cofactor;
                            terms.erase(terms.begin() +
                                        static_cast<std::ptrdiff_t>(j));
                            changed = true;
                            break;
                        }
                    }
                }
                if (changed)
                    break;
            }
        }

        // 2. Complement rules: C - C*sin(u)^2 -> C*cos(u)^2, C - C*cos(u)^2 -> C*sin(u)^2,
        //    C + C*sinh(u)^2 -> C*cosh(u)^2, -C + C*cosh(u)^2 -> C*sinh(u)^2.
        for (std::size_t i = 0; i < n && !changed; ++i) {
            for (const SqTrigTerm &ti : info[i]) {
                const Expr u = ti.arg;
                const Expr cof = ti.cofactor;
                const Expr negCof = c.neg(cof);
                for (std::size_t j = 0; j < n && !changed; ++j) {
                    if (i == j)
                        continue;
                    if (ti.kind == SqTrigKind::Sin2 && terms[j] == negCof) {
                        terms[std::min(i, j)] = c.mul(
                            {negCof, c.pow(c.func("cos", u), c.number(std::int64_t{2}))});
                        terms.erase(terms.begin() +
                                    static_cast<std::ptrdiff_t>(std::max(i, j)));
                        changed = true;
                    } else if (ti.kind == SqTrigKind::Cos2 && terms[j] == negCof) {
                        terms[std::min(i, j)] = c.mul(
                            {negCof, c.pow(c.func("sin", u), c.number(std::int64_t{2}))});
                        terms.erase(terms.begin() +
                                    static_cast<std::ptrdiff_t>(std::max(i, j)));
                        changed = true;
                    } else if (ti.kind == SqTrigKind::Sinh2 && terms[j] == cof) {
                        terms[std::min(i, j)] = c.mul(
                            {cof, c.pow(c.func("cosh", u), c.number(std::int64_t{2}))});
                        terms.erase(terms.begin() +
                                    static_cast<std::ptrdiff_t>(std::max(i, j)));
                        changed = true;
                    } else if (ti.kind == SqTrigKind::Cosh2 && terms[j] == negCof) {
                        terms[std::min(i, j)] = c.mul(
                            {cof, c.pow(c.func("sinh", u), c.number(std::int64_t{2}))});
                        terms.erase(terms.begin() +
                                    static_cast<std::ptrdiff_t>(std::max(i, j)));
                        changed = true;
                    }
                }
                if (changed)
                    break;
            }
        }

        // 1b. Double-angle cosine/cosh rules for pure degree-2 squares:
        //     B*cos(u)^2 - B*sin(u)^2 -> B*cos(2*u), B*cosh(u)^2 + B*sinh(u)^2 -> B*cosh(2*u).
        for (std::size_t i = 0; i < n && !changed; ++i) {
            for (const SqTrigTerm &ti : info[i]) {
                if (!ti.exactSq)
                    continue;
                for (std::size_t j = i + 1; j < n && !changed; ++j) {
                    for (const SqTrigTerm &tj : info[j]) {
                        if (!tj.exactSq || !(ti.arg == tj.arg))
                            continue;
                        const SqTrigTerm *pA = &ti;
                        const SqTrigTerm *pB = &tj;
                        if ((ti.kind == SqTrigKind::Cos2 &&
                             tj.kind == SqTrigKind::Sin2) ||
                            (ti.kind == SqTrigKind::Cosh2 &&
                             tj.kind == SqTrigKind::Sinh2)) {
                            std::swap(pA, pB);
                        }
                        if (pA->kind == SqTrigKind::Sin2 &&
                            pB->kind == SqTrigKind::Cos2 &&
                            pA->cofactor == c.neg(pB->cofactor)) {
                            terms[i] = c.mul(
                                {pB->cofactor,
                                 c.func("cos", c.mul({c.number(std::int64_t{2}), ti.arg}))});
                            terms.erase(terms.begin() +
                                        static_cast<std::ptrdiff_t>(j));
                            changed = true;
                            break;
                        }
                        if (pA->kind == SqTrigKind::Sinh2 &&
                            pB->kind == SqTrigKind::Cosh2 &&
                            pA->cofactor == pB->cofactor) {
                            terms[i] = c.mul(
                                {pB->cofactor,
                                 c.func("cosh", c.mul({c.number(std::int64_t{2}), ti.arg}))});
                            terms.erase(terms.begin() +
                                        static_cast<std::ptrdiff_t>(j));
                            changed = true;
                            break;
                        }
                    }
                }
                if (changed)
                    break;
            }
        }

        // 3. Logarithm combination: log(u) + log(v) -> log(simplifyRationalExpr(u*v)),
        //    log(u) - log(v) -> log(simplifyRationalExpr(u/v)) when cost decreases.
        for (std::size_t i = 0; i < terms.size() && !changed; ++i) {
            Expr uLog;
            int signI = 0;
            if (c.kind(terms[i]) == NodeKind::Func &&
                c.funcName(terms[i]) == "log") {
                uLog = c.child(terms[i], 0);
                signI = 1;
            } else if (c.kind(terms[i]) == NodeKind::Mul &&
                       c.childCount(terms[i]) == 2 &&
                       c.kind(c.child(terms[i], 0)) == NodeKind::Number &&
                       c.numberValue(c.child(terms[i], 0)) ==
                           Rational(std::int64_t{-1}) &&
                       c.kind(c.child(terms[i], 1)) == NodeKind::Func &&
                       c.funcName(c.child(terms[i], 1)) == "log") {
                uLog = c.child(c.child(terms[i], 1), 0);
                signI = -1;
            }
            if (signI == 0)
                continue;

            for (std::size_t j = i + 1; j < terms.size() && !changed; ++j) {
                Expr vLog;
                int signJ = 0;
                if (c.kind(terms[j]) == NodeKind::Func &&
                    c.funcName(terms[j]) == "log") {
                    vLog = c.child(terms[j], 0);
                    signJ = 1;
                } else if (c.kind(terms[j]) == NodeKind::Mul &&
                           c.childCount(terms[j]) == 2 &&
                           c.kind(c.child(terms[j], 0)) == NodeKind::Number &&
                           c.numberValue(c.child(terms[j], 0)) ==
                               Rational(std::int64_t{-1}) &&
                           c.kind(c.child(terms[j], 1)) == NodeKind::Func &&
                           c.funcName(c.child(terms[j], 1)) == "log") {
                    vLog = c.child(c.child(terms[j], 1), 0);
                    signJ = -1;
                }
                if (signJ == 0)
                    continue;

                Expr combinedArg;
                int outSign = 1;
                if (signI == 1 && signJ == 1) {
                    combinedArg = simplifyRationalExpr(c, c.mul({uLog, vLog}));
                } else if (signI == 1 && signJ == -1) {
                    combinedArg = simplifyRationalExpr(c, c.div(uLog, vLog));
                } else if (signI == -1 && signJ == 1) {
                    combinedArg = simplifyRationalExpr(c, c.div(vLog, uLog));
                } else {
                    combinedArg = simplifyRationalExpr(c, c.mul({uLog, vLog}));
                    outSign = -1;
                }
                if (combinedArg.isNull())
                    continue;
                Expr merged = c.func("log", combinedArg);
                Rational r;
                if (c.evalExact(merged, {}, r))
                    merged = c.number(r);
                if (outSign < 0)
                    merged = c.neg(merged);
                const Expr pairSum = c.add({terms[i], terms[j]});
                if (c.exprCost(merged) <= c.exprCost(pairSum)) {
                    terms[i] = merged;
                    terms.erase(terms.begin() + static_cast<std::ptrdiff_t>(j));
                    changed = true;
                }
            }
        }
    }

    return terms.empty() ? c.zero() : c.add(terms);
}

// Simplify a Mul node: exp(u)*exp(v) -> exp(u+v), sin(u)*cos(u)^(-1) -> tan(u),
// sinh(u)*cosh(u)^(-1) -> tanh(u), and 2*sin(u)*cos(u) -> sin(2*u).
Expr simplifyMulNode(Ctx &c, Expr e)
{
    if (c.kind(e) != NodeKind::Mul)
        return e;

    std::vector<Expr> factors;
    std::vector<Expr> expArgs;
    for (std::size_t i = 0; i < c.childCount(e); ++i) {
        const Expr ch = c.child(e, i);
        if (c.kind(ch) == NodeKind::Func && c.funcName(ch) == "exp") {
            expArgs.push_back(c.child(ch, 0));
        } else if (c.kind(ch) == NodeKind::Pow &&
                   c.kind(c.child(ch, 0)) == NodeKind::Func &&
                   c.funcName(c.child(ch, 0)) == "exp") {
            expArgs.push_back(
                c.mul({c.child(ch, 1), c.child(c.child(ch, 0), 0)}));
        } else {
            factors.push_back(ch);
        }
    }
    if (!expArgs.empty()) {
        const Expr sumExp =
            expArgs.size() == 1
                ? expArgs[0]
                : simplifyRationalExpr(c, c.add(expArgs));
        Expr expNode = c.func("exp", sumExp);
        Rational r;
        if (c.evalExact(expNode, {}, r))
            expNode = c.number(r);
        factors.push_back(expNode);
    }

    // Check double-angle sine: (2*k) * sin(u) * cos(u) -> k * sin(2*u)
    bool mergedDoubleSin = true;
    while (mergedDoubleSin) {
        mergedDoubleSin = false;
        std::size_t numIdx = factors.size();
        for (std::size_t i = 0; i < factors.size(); ++i) {
            if (c.kind(factors[i]) == NodeKind::Number) {
                const Rational &rv = c.numberValue(factors[i]);
                std::int64_t p = 0;
                if (rv.num().fitsInt64(p) && p != 0 && p % 2 == 0) {
                    numIdx = i;
                    break;
                }
            }
        }
        if (numIdx < factors.size()) {
            for (std::size_t i = 0; i < factors.size() && !mergedDoubleSin; ++i) {
                if (c.kind(factors[i]) != NodeKind::Func ||
                    c.funcName(factors[i]) != "sin")
                    continue;
                const Expr u = c.child(factors[i], 0);
                for (std::size_t j = 0; j < factors.size() && !mergedDoubleSin; ++j) {
                    if (i == j || c.kind(factors[j]) != NodeKind::Func ||
                        c.funcName(factors[j]) != "cos" ||
                        !(c.child(factors[j], 0) == u))
                        continue;
                    const Rational halfNum =
                        c.numberValue(factors[numIdx]) / Rational(std::int64_t{2});
                    factors[numIdx] = c.number(halfNum);
                    factors[i] = c.func("sin", c.mul({c.number(std::int64_t{2}), u}));
                    factors.erase(factors.begin() + static_cast<std::ptrdiff_t>(j));
                    mergedDoubleSin = true;
                }
            }
        }
    }

    // Fold sin(u)^k * cos(u)^(-k) -> tan(u)^k and sinh(u)^k * cosh(u)^(-k) -> tanh(u)^k.
    auto extractTrigPow = [&](Expr f, std::string &fnOut, Expr &argOut,
                              Rational &expOut) -> bool {
        if (c.kind(f) == NodeKind::Func) {
            fnOut = c.funcName(f);
            argOut = c.child(f, 0);
            expOut = Rational(std::int64_t{1});
            return true;
        }
        if (c.kind(f) == NodeKind::Pow &&
            c.kind(c.child(f, 0)) == NodeKind::Func &&
            c.kind(c.child(f, 1)) == NodeKind::Number) {
            fnOut = c.funcName(c.child(f, 0));
            argOut = c.child(c.child(f, 0), 0);
            expOut = c.numberValue(c.child(f, 1));
            return true;
        }
        return false;
    };

    bool mergedTan = true;
    while (mergedTan) {
        mergedTan = false;
        for (std::size_t i = 0; i < factors.size() && !mergedTan; ++i) {
            std::string fnI;
            Expr uI;
            Rational expI;
            if (!extractTrigPow(factors[i], fnI, uI, expI))
                continue;
            if (fnI != "sin" && fnI != "sinh")
                continue;
            const std::string wantCos = (fnI == "sin") ? "cos" : "cosh";
            const std::string outTan = (fnI == "sin") ? "tan" : "tanh";
            for (std::size_t j = 0; j < factors.size() && !mergedTan; ++j) {
                if (i == j)
                    continue;
                std::string fnJ;
                Expr uJ;
                Rational expJ;
                if (!extractTrigPow(factors[j], fnJ, uJ, expJ))
                    continue;
                if (fnJ == wantCos && uI == uJ && expI == -expJ &&
                    expI.signum() > 0) {
                    factors[i] = c.pow(c.func(outTan, uI), c.number(expI));
                    factors.erase(factors.begin() + static_cast<std::ptrdiff_t>(j));
                    mergedTan = true;
                }
            }
        }
    }

    return factors.empty() ? c.one() : c.mul(factors);
}

Expr simplifyFuncNode(Ctx &c, Expr e)
{
    if (c.kind(e) != NodeKind::Func)
        return e;
    const std::string &fn = c.funcName(e);
    const Expr arg = c.child(e, 0);

    Rational r;
    if (c.evalExact(e, {}, r))
        return c.number(r);

    // Canonicalize sqrt(u) -> u^(1/2)
    if (fn == "sqrt") {
        return c.pow(arg, c.number(Rational(std::int64_t{1}, BigInt(2))));
    }

    // Reflection symmetries for negative arguments: sin(-u) -> -sin(u), cos(-u) -> cos(u), etc.
    Expr posArg;
    if (extractNegativeArg(c, arg, posArg)) {
        if (fn == "sin" || fn == "tan" || fn == "cot" || fn == "csc" ||
            fn == "asin" || fn == "atan" || fn == "sinh" || fn == "tanh" ||
            fn == "coth" || fn == "csch" || fn == "asinh" || fn == "atanh") {
            return c.neg(c.func(fn, posArg));
        }
        if (fn == "cos" || fn == "sec" || fn == "cosh" || fn == "sech" ||
            fn == "abs") {
            return c.func(fn, posArg);
        }
    }

    // Inverse function compositions
    if (c.kind(arg) == NodeKind::Func) {
        const std::string &innerFn = c.funcName(arg);
        const Expr u = c.child(arg, 0);
        if ((fn == "exp" && innerFn == "log") ||
            (fn == "log" && innerFn == "exp") ||
            (fn == "sin" && innerFn == "asin") ||
            (fn == "cos" && innerFn == "acos") ||
            (fn == "tan" && innerFn == "atan") ||
            (fn == "sinh" && innerFn == "asinh") ||
            (fn == "cosh" && innerFn == "acosh") ||
            (fn == "tanh" && innerFn == "atanh")) {
            return u;
        }
        // Cross-trig of inverse trig
        const Expr u2 = c.pow(u, c.number(std::int64_t{2}));
        const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
        const Expr negHalf = c.number(Rational(std::int64_t{-1}, BigInt(2)));
        if ((fn == "cos" && innerFn == "asin") ||
            (fn == "sin" && innerFn == "acos")) {
            return c.pow(c.add({c.one(), c.neg(u2)}), half);
        }
        if (fn == "cos" && innerFn == "atan") {
            return c.pow(c.add({c.one(), u2}), negHalf);
        }
        if (fn == "sin" && innerFn == "atan") {
            return c.mul({u, c.pow(c.add({c.one(), u2}), negHalf)});
        }
        if (fn == "cosh" && innerFn == "asinh") {
            return c.pow(c.add({c.one(), u2}), half);
        }
        if (fn == "sinh" && innerFn == "acosh") {
            return c.pow(c.add({c.number(std::int64_t{-1}), u2}), half);
        }
    }

    // exp(k * log(u)) -> u^k
    if (fn == "exp" && c.kind(arg) == NodeKind::Mul && c.childCount(arg) == 2 &&
        c.kind(c.child(arg, 0)) == NodeKind::Number &&
        c.kind(c.child(arg, 1)) == NodeKind::Func &&
        c.funcName(c.child(arg, 1)) == "log") {
        return c.pow(c.child(c.child(arg, 1), 0), c.child(arg, 0));
    }

    // log(u^k) -> k * log(u) when k is an odd integer or when u is e
    if (fn == "log" && c.kind(arg) == NodeKind::Pow) {
        const Expr b = c.child(arg, 0);
        const Expr ex = c.child(arg, 1);
        if (c.kind(b) == NodeKind::Symbol && c.symbolName(b) == "e")
            return ex;
        if (c.kind(ex) == NodeKind::Number) {
            std::int64_t k = 0;
            if (c.numberValue(ex).den() == BigInt(1) &&
                c.numberValue(ex).num().fitsInt64(k) && (k % 2 != 0)) {
                return c.mul({ex, c.func("log", b)});
            }
        }
    }

    return e;
}

Expr rewriteBottomUp(Ctx &c, Expr e)
{
    if (e.isNull())
        return Expr();
    Rational r;
    if (c.evalExact(e, {}, r))
        return c.number(r);

    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        const Expr arg = rewriteBottomUp(c, c.child(e, 0));
        return simplifyFuncNode(c, c.func(c.funcName(e), arg));
    }
    case NodeKind::Pow: {
        const Expr b = rewriteBottomUp(c, c.child(e, 0));
        const Expr ex = rewriteBottomUp(c, c.child(e, 1));
        const Expr p = c.pow(b, ex);
        if (c.evalExact(p, {}, r))
            return c.number(r);
        // Exact rational square root folding: (n/q)^(k/2) when n*q is a square
        if (c.kind(b) == NodeKind::Number && c.kind(ex) == NodeKind::Number) {
            const Rational &rb = c.numberValue(b);
            const Rational &re = c.numberValue(ex);
            if (rb.signum() > 0 && re.den() == BigInt(2)) {
                const BigInt nq = rb.num() * rb.den();
                BigInt root;
                if (nq.sqrtExact(root)) {
                    const Expr sq = c.number(Rational(root, rb.den()));
                    return c.pow(sq, c.number(Rational(re.num(), BigInt(1))));
                }
            }
        }
        // exp(u)^v -> exp(u * v)
        if (c.kind(p) == NodeKind::Pow &&
            c.kind(c.child(p, 0)) == NodeKind::Func &&
            c.funcName(c.child(p, 0)) == "exp") {
            return simplifyFuncNode(
                c, c.func("exp", c.mul({c.child(c.child(p, 0), 0), c.child(p, 1)})));
        }
        return p;
    }
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(rewriteBottomUp(c, c.child(e, i)));
        return simplifyMulNode(c, c.mul(kids));
    }
    case NodeKind::Add: {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(rewriteBottomUp(c, c.child(e, i)));
        return simplifyAddNode(c, c.add(kids));
    }
    }
    return e;
}

// Convert tan/cot/sec/csc/tanh/coth/sech/csch into sin/cos and sinh/cosh,
// and optionally expand double-angle arguments 2*u into u so cross-frequency
// trig/hyperbolic identities cancel under rational normalization + Pythagoras.
Expr toSinCos(Ctx &c, Expr e, bool expandDoubleAngle)
{
    if (e.isNull())
        return Expr();
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        const Expr u = toSinCos(c, c.child(e, 0), expandDoubleAngle);
        const std::string &fn = c.funcName(e);

        // Check if `u` is `2 * v` (even integer coefficient in Mul) when expandDoubleAngle is true
        Expr halfU;
        bool isDouble = false;
        if (expandDoubleAngle && c.kind(u) == NodeKind::Mul &&
            c.childCount(u) >= 2 && c.kind(c.child(u, 0)) == NodeKind::Number) {
            const Rational &rv = c.numberValue(c.child(u, 0));
            std::int64_t p = 0;
            if (rv.den() == BigInt(1) && rv.num().fitsInt64(p) && p != 0 &&
                p % 2 == 0) {
                std::vector<Expr> rest;
                if (p / 2 != 1)
                    rest.push_back(c.number(p / 2));
                for (std::size_t i = 1; i < c.childCount(u); ++i)
                    rest.push_back(c.child(u, i));
                halfU = rest.empty() ? c.one() : c.mul(rest);
                isDouble = true;
            }
        }

        if (isDouble) {
            const Expr two = c.number(std::int64_t{2});
            if (fn == "sin") {
                return c.mul({two, c.func("sin", halfU), c.func("cos", halfU)});
            }
            if (fn == "cos") {
                return c.add({c.pow(c.func("cos", halfU), two),
                              c.neg(c.pow(c.func("sin", halfU), two))});
            }
            if (fn == "sinh") {
                return c.mul(
                    {two, c.func("sinh", halfU), c.func("cosh", halfU)});
            }
            if (fn == "cosh") {
                return c.add({c.pow(c.func("cosh", halfU), two),
                              c.pow(c.func("sinh", halfU), two)});
            }
        }

        if (fn == "tan")
            return c.div(c.func("sin", u), c.func("cos", u));
        if (fn == "cot")
            return c.div(c.func("cos", u), c.func("sin", u));
        if (fn == "sec")
            return c.pow(c.func("cos", u), c.number(std::int64_t{-1}));
        if (fn == "csc")
            return c.pow(c.func("sin", u), c.number(std::int64_t{-1}));
        if (fn == "tanh")
            return c.div(c.func("sinh", u), c.func("cosh", u));
        if (fn == "coth")
            return c.div(c.func("cosh", u), c.func("sinh", u));
        if (fn == "sech")
            return c.pow(c.func("cosh", u), c.number(std::int64_t{-1}));
        if (fn == "csch")
            return c.pow(c.func("sinh", u), c.number(std::int64_t{-1}));
        return c.func(fn, u);
    }
    case NodeKind::Pow:
        return c.pow(toSinCos(c, c.child(e, 0), expandDoubleAngle),
                     toSinCos(c, c.child(e, 1), expandDoubleAngle));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(toSinCos(c, c.child(e, i), expandDoubleAngle));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

void collectSymbols(const Ctx &c, Expr e, std::vector<Expr> &syms)
{
    if (e.isNull())
        return;
    if (c.kind(e) == NodeKind::Symbol) {
        if (std::find(syms.begin(), syms.end(), e) == syms.end())
            syms.push_back(e);
        return;
    }
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        collectSymbols(c, c.child(e, i), syms);
}

Expr singleSimplifyPass(Ctx &c, Expr e, Budget *budget)
{
    if (e.isNull() || !checkSimplifyBudget(c, budget))
        return e;

    const Expr rw = rewriteBottomUp(c, e);
    Expr best = rw;

    // Candidate 2: Rational normal form (common denominator + univariate GCD) + bottom-up rewrite.
    if (checkSimplifyBudget(c, budget)) {
        const Expr rat = simplifyRationalExpr(c, rw);
        if (!rat.isNull()) {
            const Expr ratRw = rewriteBottomUp(c, rat);
            best = pickBest(c, best, rat);
            best = pickBest(c, best, ratRw);
        }
    }

    // Candidate 3: Polynomial expansion + bottom-up rewrite (catches (sin(x)+cos(x))^2 - 2*sin(x)*cos(x) -> 1).
    if (checkSimplifyBudget(c, budget)) {
        const Expr expd = c.expand(rw);
        if (!expd.isNull()) {
            const Expr expdRw = rewriteBottomUp(c, expd);
            best = pickBest(c, best, expdRw);
        }
    }

    // Candidate 4: Trig-to-sin/cos conversion (with and without double-angle expansion)
    // + rational normal form + Pythagorean rewrite.
    for (bool expandDA : {false, true}) {
        if (!checkSimplifyBudget(c, budget))
            break;
        const Expr sc = toSinCos(c, rw, expandDA);
        if (!sc.isNull() && !(sc == rw)) {
            const Expr scRat = simplifyRationalExpr(c, sc);
            if (!scRat.isNull()) {
                const Expr scRw = rewriteBottomUp(c, scRat);
                best = pickBest(c, best, scRw);
                const Expr scRat2 = simplifyRationalExpr(c, scRw);
                if (!scRat2.isNull())
                    best = pickBest(c, best, rewriteBottomUp(c, scRat2));
            }
        }
    }

    // Candidate 5: Univariate polynomial/rational factorization (e.g. x^2 + 2*x + 1 -> (x + 1)^2).
    if (checkSimplifyBudget(c, budget)) {
        std::vector<Expr> syms;
        collectSymbols(c, best, syms);
        if (syms.size() == 1) {
            Expr factored;
            if (factorExpr(c, best, syms[0], factored) && !factored.isNull()) {
                best = pickBest(c, best, factored);
            }
        }
    }

    return best;
}

} // namespace

Expr simplify(Ctx &c, Expr e, Budget *budget)
{
    if (e.isNull())
        return Expr();
    Expr cur = e;
    for (int pass = 0; pass < 3; ++pass) {
        if (!checkSimplifyBudget(c, budget))
            break;
        const Expr next = singleSimplifyPass(c, cur, budget);
        if (next.isNull() || next == cur)
            break;
        cur = next;
    }
    return cur;
}

Expr Ctx::simplify(Expr e)
{
    return numkit::cas::simplify(*this, e, nullptr);
}

} // namespace numkit::cas
