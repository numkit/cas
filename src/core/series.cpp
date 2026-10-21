#include <numkit/cas/core/series.hpp>
#include <numkit/cas/integrate/ratint.hpp>

#include <algorithm>
#include <cstdint>
#include <vector>

namespace numkit::cas {

namespace {

bool checkSeriesBudget(const Ctx &c, Budget *budget)
{
    if (!budget)
        return true;
    return budget->step() && budget->recordArenaBytes(c.nodeCount() * 32);
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

// Fold exact rational and trivial elementary function values (sin(0)->0,
// cos(0)->1, exp(0)->1, log(1)->0, etc.) inside an expression `e`, and
// expand polynomial products so canceling symbolic coefficients (such as
// a - a -> 0) reduce canonically to zero.
Expr foldConst(Ctx &c, Expr e)
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
        const Expr arg = foldConst(c, c.child(e, 0));
        if (arg.isNull())
            return Expr();
        const Expr fn = c.func(c.funcName(e), arg);
        if (c.evalExact(fn, {}, r))
            return c.number(r);
        double dVal = 0.0;
        if (c.evalDouble(arg, {}, dVal))
            return c.simplify(fn);
        return fn;
    }
    case NodeKind::Pow: {
        const Expr b = foldConst(c, c.child(e, 0));
        const Expr ex = foldConst(c, c.child(e, 1));
        if (b.isNull() || ex.isNull())
            return Expr();
        if (c.isZero(b) && c.kind(ex) == NodeKind::Number) {
            if (c.numberValue(ex).signum() <= 0)
                return Expr();
            return c.zero();
        }
        if (c.kind(b) == NodeKind::Number && c.numberValue(b).signum() < 0 &&
            c.kind(ex) == NodeKind::Number &&
            !(c.numberValue(ex).den() == BigInt(1))) {
            std::int64_t q = 0;
            if (!c.numberValue(ex).den().fitsInt64(q) || q % 2 == 0)
                return Expr();
        }
        return c.expand(c.pow(b, ex));
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr k = foldConst(c, c.child(e, i));
            if (k.isNull())
                return Expr();
            kids.push_back(k);
        }
        const Expr built =
            c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
        return c.expand(built);
    }
    }
    return e;
}

bool isZeroCoeff(Ctx &c, Expr e)
{
    if (e.isNull())
        return false;
    if (c.isZero(e))
        return true;
    const Expr f = foldConst(c, e);
    return !f.isNull() && c.isZero(f);
}

// Substitute `from -> to` while folding constants and checking for poles
// (0^negative, log(0)). Returns null Expr if substitution hits a pole.
Expr safeSubsAndFold(Ctx &c, Expr e, Expr from, Expr to)
{
    if (e.isNull())
        return Expr();
    if (e == from)
        return to;
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        const Expr a = safeSubsAndFold(c, c.child(e, 0), from, to);
        if (a.isNull())
            return Expr();
        const std::string &fn = c.funcName(e);
        if ((fn == "log" || fn == "Ei" || fn == "Ci") && isZeroCoeff(c, a))
            return Expr();
        if (fn == "li" &&
            isZeroCoeff(c, c.add({a, c.number(std::int64_t{-1})})))
            return Expr();
        return foldConst(c, c.func(fn, a));
    }
    case NodeKind::Pow: {
        const Expr b = safeSubsAndFold(c, c.child(e, 0), from, to);
        const Expr ex = safeSubsAndFold(c, c.child(e, 1), from, to);
        if (b.isNull() || ex.isNull())
            return Expr();
        if (isZeroCoeff(c, b)) {
            if (c.kind(ex) != NodeKind::Number ||
                c.numberValue(ex).signum() <= 0)
                return Expr();
            return c.zero();
        }
        return foldConst(c, c.pow(b, ex));
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr k = safeSubsAndFold(c, c.child(e, i), from, to);
            if (k.isNull())
                return Expr();
            kids.push_back(k);
        }
        return foldConst(
            c, c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids));
    }
    }
    return Expr();
}

// Truncated Laurent series S(t) = sum_{k=0}^{coeffs.size()-1} coeffs[k] t^{val+k} + O(t^{maxDeg+1}).
struct Laurent
{
    int val = 0;
    int maxDeg = 0;
    std::vector<Expr> coeffs;
};

void normalizeSeries(Ctx &c, Laurent &s)
{
    for (Expr &coef : s.coeffs)
        coef = foldConst(c, coef);
    while (!s.coeffs.empty() && isZeroCoeff(c, s.coeffs.front())) {
        s.coeffs.erase(s.coeffs.begin());
        ++s.val;
    }
    if (s.coeffs.empty()) {
        s.val = s.maxDeg + 1;
        return;
    }
    if (s.val > s.maxDeg) {
        s.coeffs.clear();
        s.val = s.maxDeg + 1;
        return;
    }
    const std::size_t maxCount =
        static_cast<std::size_t>(s.maxDeg - s.val + 1);
    if (s.coeffs.size() > maxCount)
        s.coeffs.resize(maxCount);
}

Expr coeffAt(Ctx &c, const Laurent &s, int deg)
{
    if (deg < s.val)
        return c.zero();
    const int idx = deg - s.val;
    if (idx < 0 || static_cast<std::size_t>(idx) >= s.coeffs.size())
        return c.zero();
    return s.coeffs[static_cast<std::size_t>(idx)];
}

Laurent makeConstSeries(Ctx &c, Expr val, int maxDeg)
{
    Laurent s;
    s.val = 0;
    s.maxDeg = maxDeg;
    s.coeffs.push_back(foldConst(c, val));
    normalizeSeries(c, s);
    return s;
}

Laurent addSeries(Ctx &c, const Laurent &a, const Laurent &b)
{
    Laurent out;
    out.maxDeg = std::min(a.maxDeg, b.maxDeg);
    out.val = std::min(a.val, b.val);
    if (out.val > out.maxDeg) {
        out.val = out.maxDeg + 1;
        return out;
    }
    out.coeffs.reserve(static_cast<std::size_t>(out.maxDeg - out.val + 1));
    for (int d = out.val; d <= out.maxDeg; ++d) {
        out.coeffs.push_back(
            foldConst(c, c.add({coeffAt(c, a, d), coeffAt(c, b, d)})));
    }
    normalizeSeries(c, out);
    return out;
}

Laurent scaleSeries(Ctx &c, const Laurent &a, Expr factor)
{
    Laurent out = a;
    for (Expr &coef : out.coeffs)
        coef = foldConst(c, c.mul({factor, coef}));
    normalizeSeries(c, out);
    return out;
}

Laurent mulSeries(Ctx &c, const Laurent &a, const Laurent &b)
{
    Laurent out;
    out.maxDeg = std::min(a.maxDeg + b.val, b.maxDeg + a.val);
    if (a.coeffs.empty() || b.coeffs.empty()) {
        out.val = out.maxDeg + 1;
        return out;
    }
    out.val = a.val + b.val;
    if (out.val > out.maxDeg) {
        out.val = out.maxDeg + 1;
        return out;
    }
    const int len = out.maxDeg - out.val + 1;
    out.coeffs.assign(static_cast<std::size_t>(len), c.zero());
    for (int i = 0; i < static_cast<int>(a.coeffs.size()) && i < len; ++i) {
        if (isZeroCoeff(c, a.coeffs[static_cast<std::size_t>(i)]))
            continue;
        for (int j = 0;
             j < static_cast<int>(b.coeffs.size()) && i + j < len; ++j) {
            if (isZeroCoeff(c, b.coeffs[static_cast<std::size_t>(j)]))
                continue;
            const Expr prod =
                c.mul({a.coeffs[static_cast<std::size_t>(i)],
                       b.coeffs[static_cast<std::size_t>(j)]});
            out.coeffs[static_cast<std::size_t>(i + j)] = foldConst(
                c, c.add({out.coeffs[static_cast<std::size_t>(i + j)], prod}));
        }
    }
    normalizeSeries(c, out);
    return out;
}

bool invSeries(Ctx &c, const Laurent &b, Laurent &out)
{
    if (b.coeffs.empty() || isZeroCoeff(c, b.coeffs.front()))
        return false; // division by series that is identically 0 up to its precision
    const int relPrec = b.maxDeg - b.val;
    if (relPrec < 0)
        return false;
    const Expr b0 = b.coeffs.front();
    const Expr invB0 = foldConst(c, c.pow(b0, c.number(std::int64_t{-1})));
    if (invB0.isNull())
        return false;

    out.val = -b.val;
    out.maxDeg = -b.val + relPrec;
    out.coeffs.assign(static_cast<std::size_t>(relPrec + 1), c.zero());
    out.coeffs[0] = invB0;
    for (int k = 1; k <= relPrec; ++k) {
        std::vector<Expr> terms;
        for (int j = 1; j <= k; ++j) {
            const Expr bj = coeffAt(c, b, b.val + j);
            if (!isZeroCoeff(c, bj) &&
                !isZeroCoeff(c, out.coeffs[static_cast<std::size_t>(k - j)])) {
                terms.push_back(
                    c.mul({bj, out.coeffs[static_cast<std::size_t>(k - j)]}));
            }
        }
        if (!terms.empty()) {
            out.coeffs[static_cast<std::size_t>(k)] =
                foldConst(c, c.mul({c.neg(invB0), c.add(terms)}));
        }
    }
    normalizeSeries(c, out);
    return true;
}

bool powIntSeries(Ctx &c, const Laurent &base, std::int64_t k, int relPrec,
                  Laurent &out)
{
    if (k == 0) {
        out = makeConstSeries(c, c.one(), relPrec);
        return true;
    }
    Laurent cur = base;
    if (k < 0) {
        if (!invSeries(c, base, cur))
            return false;
        k = -k;
    }
    bool hasRes = false;
    Laurent res;
    std::uint64_t exp = static_cast<std::uint64_t>(k);
    while (exp > 0) {
        if (exp & 1ULL) {
            res = hasRes ? mulSeries(c, res, cur) : cur;
            hasRes = true;
        }
        exp >>= 1ULL;
        if (exp > 0)
            cur = mulSeries(c, cur, cur);
    }
    out = res;
    return true;
}

bool powRatSeries(Ctx &c, const Laurent &base, const Rational &r, int relPrec,
                  Laurent &out)
{
    std::int64_t p = 0, q = 0;
    if (!r.num().fitsInt64(p) || !r.den().fitsInt64(q) || q <= 0)
        return false;
    if (q == 1)
        return powIntSeries(c, base, p, relPrec, out);
    if (base.coeffs.empty()) {
        if (p <= 0)
            return false;
        out.val = (base.maxDeg * static_cast<int>(p)) / static_cast<int>(q) + 1;
        out.maxDeg = out.val - 1;
        out.coeffs.clear();
        return true;
    }
    if ((static_cast<std::int64_t>(base.val) * p) % q != 0)
        return false; // fractional branch point in t
    const int outVal =
        static_cast<int>((static_cast<std::int64_t>(base.val) * p) / q);
    const int L = base.maxDeg - base.val;
    if (L < 0)
        return false;

    const Expr b0 = base.coeffs.front();
    const Expr c0 = foldConst(c, c.pow(b0, c.number(r)));
    if (c0.isNull())
        return false;
    const Expr invB0 = foldConst(c, c.pow(b0, c.number(std::int64_t{-1})));
    if (invB0.isNull())
        return false;

    // u(t) = (base / (b0 * t^val)) - 1, which has valuation >= 1 and maxDeg = L.
    Laurent u;
    u.val = 1;
    u.maxDeg = L;
    for (int j = 1; j <= L; ++j)
        u.coeffs.push_back(foldConst(c, c.mul({invB0, coeffAt(c, base, base.val + j)})));
    normalizeSeries(c, u);

    // Binomial expansion: (1 + u)^r = sum_{k=0}^L binom(r, k) u^k.
    Laurent sum = makeConstSeries(c, c.one(), L);
    Laurent uk = u;
    Rational binom(1);
    for (int k = 1; k <= L && !uk.coeffs.empty(); ++k) {
        binom = binom * (r - Rational(static_cast<std::int64_t>(k - 1))) /
                Rational(static_cast<std::int64_t>(k));
        sum = addSeries(c, sum, scaleSeries(c, uk, c.number(binom)));
        if (k < L)
            uk = mulSeries(c, uk, u);
    }

    // Multiply by c0 * t^outVal.
    out = scaleSeries(c, sum, c0);
    if (!out.coeffs.empty())
        out.val += outVal;
    out.maxDeg = L + outVal;
    normalizeSeries(c, out);
    return true;
}

Laurent diffSeries(Ctx &c, const Laurent &a)
{
    Laurent out;
    out.maxDeg = a.maxDeg - 1;
    if (a.coeffs.empty()) {
        out.val = out.maxDeg + 1;
        return out;
    }
    out.val = a.val - 1;
    for (std::size_t i = 0; i < a.coeffs.size(); ++i) {
        const int deg = a.val + static_cast<int>(i);
        if (deg == 0) {
            out.coeffs.push_back(c.zero());
        } else {
            out.coeffs.push_back(foldConst(
                c, c.mul({c.number(static_cast<std::int64_t>(deg)), a.coeffs[i]})));
        }
    }
    normalizeSeries(c, out);
    return out;
}

// Integrate a Taylor series G(t) (requires val >= 0) from 0 to t:
// int_0^t (sum_{d>=0} g_d tau^d) dtau = sum_{d>=0} g_d/(d+1) t^{d+1}.
bool integrateSeriesZeroConst(Ctx &c, const Laurent &g, Laurent &out)
{
    if (!g.coeffs.empty() && g.val < 0)
        return false;
    out.maxDeg = g.maxDeg + 1;
    if (g.coeffs.empty()) {
        out.val = out.maxDeg + 1;
        return true;
    }
    out.val = g.val + 1;
    out.coeffs.reserve(g.coeffs.size());
    for (std::size_t i = 0; i < g.coeffs.size(); ++i) {
        const int d = g.val + static_cast<int>(i);
        out.coeffs.push_back(foldConst(
            c, c.mul({c.number(Rational(std::int64_t{1}, BigInt(d + 1))),
                      g.coeffs[i]})));
    }
    normalizeSeries(c, out);
    return true;
}

int exprSign(Ctx &c, Expr e)
{
    if (e.isNull())
        return 0;
    Rational r;
    if (c.evalExact(e, {}, r))
        return r.signum();
    if (c.isAssumedPositive(e))
        return +1;
    if (c.isAssumedNegative(e))
        return -1;
    double dVal = 0.0;
    if (c.evalDouble(e, {}, dVal)) {
        if (dVal > 1e-12)
            return +1;
        if (dVal < -1e-12)
            return -1;
    }
    return 0;
}

bool evalFuncSeries(Ctx &c, const std::string &fn, const Laurent &arg,
                    Laurent &out, bool positiveT = false)
{
    if (fn == "sqrt") {
        return powRatSeries(c, arg, Rational(std::int64_t{1}, BigInt(2)),
                            arg.maxDeg, out);
    }
    if (!arg.coeffs.empty() && arg.val < 0) {
        if (!positiveT && (-arg.val) % 2 != 0)
            return false; // odd pole changes sign across two-sided t -> 0
        const int sgn = exprSign(c, arg.coeffs.front());
        if (sgn == 0)
            return false;
        const int highDeg = std::max(32, -arg.val * 8);
        if (fn == "atan") {
            Laurent invArg, atanInv;
            if (!invSeries(c, arg, invArg) ||
                !evalFuncSeries(c, "atan", invArg, atanInv, positiveT))
                return false;
            const Expr halfPi = c.mul(
                {c.number(Rational(static_cast<std::int64_t>(sgn), BigInt(2))),
                 c.symbol("pi")});
            out = addSeries(
                c, makeConstSeries(c, halfPi, atanInv.maxDeg),
                scaleSeries(c, atanInv, c.number(std::int64_t{-1})));
            return true;
        }
        if (fn == "acot") {
            Laurent invArg, atanInv;
            if (!invSeries(c, arg, invArg) ||
                !evalFuncSeries(c, "atan", invArg, atanInv, positiveT))
                return false;
            if (sgn > 0) {
                out = atanInv;
            } else {
                out = addSeries(
                    c, makeConstSeries(c, c.symbol("pi"), atanInv.maxDeg),
                    atanInv);
            }
            return true;
        }
        if (fn == "exp" && sgn < 0) {
            out = makeConstSeries(c, c.zero(), highDeg);
            return true;
        }
        if (fn == "tanh" || fn == "coth" || fn == "erf") {
            out = makeConstSeries(
                c, c.number(static_cast<std::int64_t>(sgn)), highDeg);
            return true;
        }
        if (fn == "erfc") {
            out = makeConstSeries(
                c, c.number(static_cast<std::int64_t>(1 - sgn)), highDeg);
            return true;
        }
        if (fn == "Si") {
            const Expr halfPi = c.mul(
                {c.number(Rational(static_cast<std::int64_t>(sgn), BigInt(2))),
                 c.symbol("pi")});
            out = makeConstSeries(c, halfPi, highDeg);
            return true;
        }
        if (fn == "Ci" && sgn > 0) {
            out = makeConstSeries(c, c.zero(), highDeg);
            return true;
        }
        if (fn == "Ei" && sgn < 0) {
            out = makeConstSeries(c, c.zero(), highDeg);
            return true;
        }
        if (fn == "FresnelS" || fn == "FresnelC") {
            out = makeConstSeries(
                c,
                c.number(Rational(static_cast<std::int64_t>(sgn), BigInt(2))),
                highDeg);
            return true;
        }
        if (fn == "sech" || fn == "csch") {
            out = makeConstSeries(c, c.zero(), highDeg);
            return true;
        }
        return false; // essential singularity / pole inside transcendental
    }
    const int L = arg.maxDeg;
    if (L < 0)
        return false;
    const Expr c0 = foldConst(c, coeffAt(c, arg, 0));
    if (c0.isNull())
        return false;

    // u(t) = arg(t) - c0, with valuation >= 1 and maxDeg = L.
    Laurent u = addSeries(c, arg, makeConstSeries(c, c.neg(c0), L));
    if (fn == "exp") {
        const Expr expC0 = foldConst(c, c.func("exp", c0));
        Laurent sum = makeConstSeries(c, c.one(), L);
        Laurent uk = u;
        BigInt fact(1);
        for (int k = 1; k <= L && !uk.coeffs.empty(); ++k) {
            fact = fact * BigInt(k);
            sum = addSeries(
                c, sum, scaleSeries(c, uk, c.number(Rational(BigInt(1), fact))));
            if (k < L)
                uk = mulSeries(c, uk, u);
        }
        out = scaleSeries(c, sum, expC0);
        return true;
    }
    if (fn == "log") {
        if (isZeroCoeff(c, c0))
            return false; // log(0 + ...) has a logarithmic branch point
        const Expr logC0 = foldConst(c, c.func("log", c0));
        const Expr invC0 = foldConst(c, c.pow(c0, c.number(std::int64_t{-1})));
        if (invC0.isNull())
            return false;
        const Laurent w = scaleSeries(c, u, invC0);
        Laurent sum = makeConstSeries(c, logC0, L);
        Laurent wk = w;
        for (int k = 1; k <= L && !wk.coeffs.empty(); ++k) {
            const Rational coef((k % 2 == 1) ? std::int64_t{1} : std::int64_t{-1},
                                BigInt(k));
            sum = addSeries(c, sum, scaleSeries(c, wk, c.number(coef)));
            if (k < L)
                wk = mulSeries(c, wk, w);
        }
        out = sum;
        return true;
    }
    if (fn == "sin" || fn == "cos" || fn == "sinh" || fn == "cosh") {
        const bool hyp = (fn == "sinh" || fn == "cosh");
        Laurent sU = makeConstSeries(c, c.zero(), L);
        Laurent cU = makeConstSeries(c, c.one(), L);
        Laurent uk = u;
        BigInt fact(1);
        for (int k = 1; k <= L && !uk.coeffs.empty(); ++k) {
            fact = fact * BigInt(k);
            const std::int64_t sign =
                (!hyp && ((k / 2) % 2 == 1)) ? std::int64_t{-1} : std::int64_t{1};
            const Expr coef = c.number(Rational(sign, fact));
            if (k % 2 == 1)
                sU = addSeries(c, sU, scaleSeries(c, uk, coef));
            else
                cU = addSeries(c, cU, scaleSeries(c, uk, coef));
            if (k < L)
                uk = mulSeries(c, uk, u);
        }
        if (fn == "sin") {
            const Expr s0 = foldConst(c, c.func("sin", c0));
            const Expr cs0 = foldConst(c, c.func("cos", c0));
            out = addSeries(c, scaleSeries(c, cU, s0), scaleSeries(c, sU, cs0));
            return true;
        }
        if (fn == "cos") {
            const Expr s0 = foldConst(c, c.func("sin", c0));
            const Expr cs0 = foldConst(c, c.func("cos", c0));
            out = addSeries(c, scaleSeries(c, cU, cs0),
                            scaleSeries(c, sU, c.neg(s0)));
            return true;
        }
        if (fn == "sinh") {
            const Expr sh0 = foldConst(c, c.func("sinh", c0));
            const Expr ch0 = foldConst(c, c.func("cosh", c0));
            out = addSeries(c, scaleSeries(c, cU, sh0), scaleSeries(c, sU, ch0));
            return true;
        }
        const Expr sh0 = foldConst(c, c.func("sinh", c0));
        const Expr ch0 = foldConst(c, c.func("cosh", c0));
        out = addSeries(c, scaleSeries(c, cU, ch0), scaleSeries(c, sU, sh0));
        return true;
    }
    if (fn == "tan" || fn == "cot" || fn == "sec" || fn == "csc") {
        Laurent s, cs, inv;
        if (!evalFuncSeries(c, "sin", arg, s) ||
            !evalFuncSeries(c, "cos", arg, cs))
            return false;
        if (fn == "tan") {
            return invSeries(c, cs, inv) && ((out = mulSeries(c, s, inv)), true);
        }
        if (fn == "cot") {
            return invSeries(c, s, inv) && ((out = mulSeries(c, cs, inv)), true);
        }
        if (fn == "sec") {
            return invSeries(c, cs, out);
        }
        return invSeries(c, s, out);
    }
    if (fn == "tanh" || fn == "coth" || fn == "sech" || fn == "csch") {
        Laurent sh, ch, inv;
        if (!evalFuncSeries(c, "sinh", arg, sh) ||
            !evalFuncSeries(c, "cosh", arg, ch))
            return false;
        if (fn == "tanh") {
            return invSeries(c, ch, inv) && ((out = mulSeries(c, sh, inv)), true);
        }
        if (fn == "coth") {
            return invSeries(c, sh, inv) && ((out = mulSeries(c, ch, inv)), true);
        }
        if (fn == "sech") {
            return invSeries(c, ch, out);
        }
        return invSeries(c, sh, out);
    }
    if (fn == "atan" || fn == "atanh" || fn == "asin" || fn == "acos" ||
        fn == "asinh" || fn == "acosh") {
        const Laurent dA = diffSeries(c, arg);
        const Laurent a2 = mulSeries(c, arg, arg);
        const Laurent one = makeConstSeries(c, c.one(), L);
        Laurent factor;
        if (fn == "atan") {
            if (!invSeries(c, addSeries(c, one, a2), factor))
                return false;
        } else if (fn == "atanh") {
            if (!invSeries(c, addSeries(c, one, scaleSeries(c, a2, c.number(std::int64_t{-1}))),
                           factor))
                return false;
        } else if (fn == "asin" || fn == "acos") {
            if (!powRatSeries(
                    c, addSeries(c, one, scaleSeries(c, a2, c.number(std::int64_t{-1}))),
                    Rational(std::int64_t{-1}, BigInt(2)), L, factor))
                return false;
            if (fn == "acos")
                factor = scaleSeries(c, factor, c.number(std::int64_t{-1}));
        } else if (fn == "asinh") {
            if (!powRatSeries(c, addSeries(c, one, a2),
                              Rational(std::int64_t{-1}, BigInt(2)), L, factor))
                return false;
        } else {
            // acosh: 1 / sqrt(A^2 - 1)
            if (!powRatSeries(
                    c, addSeries(c, a2, makeConstSeries(c, c.number(std::int64_t{-1}), L)),
                    Rational(std::int64_t{-1}, BigInt(2)), L, factor))
                return false;
        }
        Laurent intPart;
        if (!integrateSeriesZeroConst(c, mulSeries(c, dA, factor), intPart))
            return false;
        const Expr f0 = foldConst(c, c.func(fn, c0));
        out = addSeries(c, makeConstSeries(c, f0, L), intPart);
        return true;
    }
    if (fn == "erf" || fn == "erfc" || fn == "erfi") {
        const Laurent dA = diffSeries(c, arg);
        const Laurent a2 = mulSeries(c, arg, arg);
        const Laurent expArg =
            (fn == "erfi") ? a2 : scaleSeries(c, a2, c.number(std::int64_t{-1}));
        Laurent expS;
        if (!evalFuncSeries(c, "exp", expArg, expS, positiveT))
            return false;
        const Expr twoOverSqrtPi = c.mul(
            {c.number(std::int64_t{fn == "erfc" ? -2 : 2}),
             c.pow(c.symbol("pi"),
                   c.number(Rational(std::int64_t{-1}, BigInt(2))))});
        Laurent intPart;
        if (!integrateSeriesZeroConst(
                c, scaleSeries(c, mulSeries(c, dA, expS), twoOverSqrtPi),
                intPart))
            return false;
        const Expr f0 = foldConst(c, c.func(fn, c0));
        out = addSeries(c, makeConstSeries(c, f0, L), intPart);
        return true;
    }
    if (fn == "Si") {
        if (isZeroCoeff(c, c0)) {
            Laurent sum = makeConstSeries(c, c.zero(), L);
            const Laurent u2 = mulSeries(c, u, u);
            Laurent upow = u;
            BigInt fact(1);
            for (int m = 0; 2 * m + 1 <= L && !upow.coeffs.empty(); ++m) {
                if (m > 0) {
                    fact = fact * BigInt(2 * m) * BigInt(2 * m + 1);
                }
                const std::int64_t sgn =
                    (m % 2 == 0) ? std::int64_t{1} : std::int64_t{-1};
                const Expr coef = c.number(
                    Rational(sgn, fact * BigInt(2 * m + 1)));
                sum = addSeries(c, sum, scaleSeries(c, upow, coef));
                if (2 * (m + 1) + 1 <= L)
                    upow = mulSeries(c, upow, u2);
            }
            out = sum;
            return true;
        }
        Laurent sinA, invA, intPart;
        if (!evalFuncSeries(c, "sin", arg, sinA, positiveT) ||
            !invSeries(c, arg, invA))
            return false;
        const Laurent dA = diffSeries(c, arg);
        if (!integrateSeriesZeroConst(
                c, mulSeries(c, mulSeries(c, sinA, invA), dA), intPart))
            return false;
        const Expr f0 = foldConst(c, c.func(fn, c0));
        out = addSeries(c, makeConstSeries(c, f0, L), intPart);
        return true;
    }
    if (fn == "Ci" || fn == "Ei") {
        if (isZeroCoeff(c, c0))
            return false;
        Laurent numS, invA, intPart;
        const std::string numFn = (fn == "Ci") ? "cos" : "exp";
        if (!evalFuncSeries(c, numFn, arg, numS, positiveT) ||
            !invSeries(c, arg, invA))
            return false;
        const Laurent dA = diffSeries(c, arg);
        if (!integrateSeriesZeroConst(
                c, mulSeries(c, mulSeries(c, numS, invA), dA), intPart))
            return false;
        const Expr f0 = foldConst(c, c.func(fn, c0));
        out = addSeries(c, makeConstSeries(c, f0, L), intPart);
        return true;
    }
    if (fn == "li") {
        if (isZeroCoeff(c, c0) ||
            isZeroCoeff(c, c.add({c0, c.number(std::int64_t{-1})})))
            return false;
        Laurent logA, invLogA, intPart;
        if (!evalFuncSeries(c, "log", arg, logA, positiveT) ||
            !invSeries(c, logA, invLogA))
            return false;
        const Laurent dA = diffSeries(c, arg);
        if (!integrateSeriesZeroConst(c, mulSeries(c, invLogA, dA), intPart))
            return false;
        const Expr f0 = foldConst(c, c.func(fn, c0));
        out = addSeries(c, makeConstSeries(c, f0, L), intPart);
        return true;
    }
    if (fn == "FresnelS" || fn == "FresnelC") {
        const Laurent dA = diffSeries(c, arg);
        const Laurent a2 = mulSeries(c, arg, arg);
        const Expr halfPi = c.mul(
            {c.number(Rational(std::int64_t{1}, BigInt(2))), c.symbol("pi")});
        const Laurent trigArg = scaleSeries(c, a2, halfPi);
        Laurent trigS, intPart;
        if (!evalFuncSeries(c, fn == "FresnelS" ? "sin" : "cos", trigArg, trigS,
                            positiveT) ||
            !integrateSeriesZeroConst(c, mulSeries(c, dA, trigS), intPart))
            return false;
        const Expr f0 = foldConst(c, c.func(fn, c0));
        out = addSeries(c, makeConstSeries(c, f0, L), intPart);
        return true;
    }
    return false;
}

bool computeLaurent(Ctx &c, Expr e, Expr var, Expr x0, int maxDeg,
                    Budget *budget, Laurent &out, bool positiveT = false)
{
    if (!checkSeriesBudget(c, budget))
        return false;
    if (!mentionsSymbol(c, e, var)) {
        out = makeConstSeries(c, e, maxDeg);
        return true;
    }
    if (e == var) {
        // var = x0 + 1*t
        Laurent cPart = makeConstSeries(c, x0, maxDeg);
        Laurent tPart;
        tPart.val = 1;
        tPart.maxDeg = maxDeg;
        if (maxDeg >= 1)
            tPart.coeffs.push_back(c.one());
        normalizeSeries(c, tPart);
        out = addSeries(c, cPart, tPart);
        return true;
    }

    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        out = makeConstSeries(c, e, maxDeg);
        return true;
    case NodeKind::Add: {
        Laurent acc = makeConstSeries(c, c.zero(), maxDeg);
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            Laurent term;
            if (!computeLaurent(c, c.child(e, i), var, x0, maxDeg, budget, term,
                                positiveT))
                return false;
            acc = addSeries(c, acc, term);
        }
        out = acc;
        return true;
    }
    case NodeKind::Mul: {
        Laurent acc = makeConstSeries(c, c.one(), maxDeg);
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            Laurent factor;
            if (!computeLaurent(c, c.child(e, i), var, x0, maxDeg, budget, factor,
                                positiveT))
                return false;
            acc = mulSeries(c, acc, factor);
        }
        out = acc;
        return true;
    }
    case NodeKind::Pow: {
        const Expr baseExpr = c.child(e, 0);
        const Expr expExpr = c.child(e, 1);
        if (!mentionsSymbol(c, expExpr, var)) {
            const Expr foldedExp = foldConst(c, expExpr);
            if (!foldedExp.isNull() && c.kind(foldedExp) == NodeKind::Number) {
                Laurent bSeries;
                if (!computeLaurent(c, baseExpr, var, x0, maxDeg, budget, bSeries,
                                    positiveT))
                    return false;
                return powRatSeries(c, bSeries, c.numberValue(foldedExp), maxDeg,
                                    out);
            }
        }
        // General power b(x)^e(x) = exp(e(x) * log(b(x)))
        Laurent bSeries, logB, eSeries;
        if (!computeLaurent(c, baseExpr, var, x0, maxDeg, budget, bSeries,
                            positiveT) ||
            !evalFuncSeries(c, "log", bSeries, logB, positiveT) ||
            !computeLaurent(c, expExpr, var, x0, maxDeg, budget, eSeries,
                            positiveT))
            return false;
        return evalFuncSeries(c, "exp", mulSeries(c, eSeries, logB), out,
                              positiveT);
    }
    case NodeKind::Func: {
        Laurent argSeries;
        if (!computeLaurent(c, c.child(e, 0), var, x0, maxDeg, budget, argSeries,
                            positiveT))
            return false;
        return evalFuncSeries(c, c.funcName(e), argSeries, out, positiveT);
    }
    }
    return false;
}

Expr renderSeries(Ctx &c, const Laurent &s, Expr var, Expr x0, int order)
{
    const Expr dx = c.isZero(x0) ? var : c.add({var, c.neg(x0)});
    std::vector<Expr> terms;
    for (std::size_t i = 0; i < s.coeffs.size(); ++i) {
        const int deg = s.val + static_cast<int>(i);
        if (deg > order)
            break;
        const Expr &coef = s.coeffs[i];
        if (isZeroCoeff(c, coef))
            continue;
        if (deg == 0) {
            terms.push_back(coef);
        } else if (deg == 1) {
            terms.push_back(c.mul({coef, dx}));
        } else {
            terms.push_back(
                c.mul({coef, c.pow(dx, c.number(static_cast<std::int64_t>(deg)))}));
        }
    }
    return terms.empty() ? c.zero() : c.add(terms);
}

// Fallback iterated differentiation Taylor builder: sum_{k=0}^{order} f^(k)(x0)/k! (x - x0)^k.
Expr taylorByDiffFallback(Ctx &c, Expr f, Expr var, Expr x0, int order,
                          Budget *budget)
{
    const Expr dx = c.isZero(x0) ? var : c.add({var, c.neg(x0)});
    std::vector<Expr> terms;
    Expr cur = f;
    BigInt fact(1);
    for (int k = 0; k <= order; ++k) {
        if (!checkSeriesBudget(c, budget))
            return Expr();
        if (k > 0) {
            cur = c.diff(cur, var);
            fact = fact * BigInt(k);
        }
        const Expr atX0 = safeSubsAndFold(c, cur, var, x0);
        if (atX0.isNull())
            return Expr();
        if (!isZeroCoeff(c, atX0)) {
            const Expr coef = foldConst(
                c, c.mul({c.number(Rational(BigInt(1), fact)), atX0}));
            if (k == 0)
                terms.push_back(coef);
            else if (k == 1)
                terms.push_back(c.mul({coef, dx}));
            else
                terms.push_back(
                    c.mul({coef, c.pow(dx, c.number(static_cast<std::int64_t>(k)))}));
        }
    }
    return terms.empty() ? c.zero() : c.add(terms);
}

} // namespace

Expr taylor(Ctx &c, Expr f, Expr var, Expr x0, int order, Budget *budget)
{
    if (f.isNull() || var.isNull() || x0.isNull() || order < 0)
        return Expr();
    // Try Laurent expansion with cushion +8 (and retry +16 if deep cancellation
    // reduced reliable degree below `order`).
    for (int pad : {8, 16}) {
        Laurent s;
        if (computeLaurent(c, f, var, x0, order + pad, budget, s)) {
            if (!s.coeffs.empty() && s.val < 0)
                return Expr(); // pole at x0: no Taylor expansion
            if (s.maxDeg >= order)
                return renderSeries(c, s, var, x0, order);
        }
        if (budget && !budget->ok())
            return Expr();
    }
    return taylorByDiffFallback(c, f, var, x0, order, budget);
}

Expr laurent(Ctx &c, Expr f, Expr var, Expr x0, int order, Budget *budget)
{
    if (f.isNull() || var.isNull() || x0.isNull())
        return Expr();
    for (int pad : {8, 16}) {
        Laurent s;
        if (computeLaurent(c, f, var, x0, order + pad, budget, s) &&
            s.maxDeg >= order) {
            return renderSeries(c, s, var, x0, order);
        }
        if (budget && !budget->ok())
            return Expr();
    }
    return Expr();
}

namespace {

// Combine linear combinations sum_i r_i * log(u_i) (r_i in Q) inside Add nodes
// into (1/q) * log(prod_i u_i^(q * r_i)), canceling inf - inf log poles.
Expr combineLogsForLimit(Ctx &c, Expr e)
{
    if (e.isNull())
        return Expr();
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func:
        return c.func(c.funcName(e), combineLogsForLimit(c, c.child(e, 0)));
    case NodeKind::Pow:
        return c.pow(combineLogsForLimit(c, c.child(e, 0)),
                     combineLogsForLimit(c, c.child(e, 1)));
    case NodeKind::Mul: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            ch.push_back(combineLogsForLimit(c, c.child(e, i)));
        return c.mul(ch);
    }
    case NodeKind::Add: {
        std::vector<Expr> otherTerms;
        std::vector<std::pair<Rational, Expr>> logTerms;
        auto matchRatLog = [&](Expr t, Rational &rOut, Expr &uOut) -> bool {
            if (c.kind(t) == NodeKind::Func && c.funcName(t) == "log") {
                rOut = Rational(std::int64_t{1});
                uOut = c.child(t, 0);
                return true;
            }
            if (c.kind(t) == NodeKind::Mul && c.childCount(t) == 2 &&
                c.kind(c.child(t, 0)) == NodeKind::Number &&
                c.kind(c.child(t, 1)) == NodeKind::Func &&
                c.funcName(c.child(t, 1)) == "log") {
                rOut = c.numberValue(c.child(t, 0));
                uOut = c.child(c.child(t, 1), 0);
                return true;
            }
            return false;
        };
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr ti = combineLogsForLimit(c, c.child(e, i));
            Rational r;
            Expr u;
            if (matchRatLog(ti, r, u))
                logTerms.push_back({r, u});
            else
                otherTerms.push_back(ti);
        }
        if (logTerms.size() >= 2) {
            BigInt qLcm(1);
            for (const auto &kv : logTerms) {
                const BigInt g = BigInt::gcd(qLcm, kv.first.den());
                qLcm = (qLcm / g) * kv.first.den();
            }
            std::vector<Expr> prodFactors;
            prodFactors.reserve(logTerms.size());
            for (const auto &kv : logTerms) {
                const BigInt m = kv.first.num() * (qLcm / kv.first.den());
                prodFactors.push_back(
                    c.pow(kv.second, c.number(Rational(m, BigInt(1)))));
            }
            const Expr combinedLog = c.mul(
                {c.number(Rational(BigInt(1), qLcm)),
                 c.func("log", c.mul(prodFactors))});
            otherTerms.push_back(combinedLog);
        } else {
            for (const auto &kv : logTerms)
                otherTerms.push_back(
                    c.mul({c.number(kv.first), c.func("log", kv.second)}));
        }
        return otherTerms.empty() ? c.zero() : c.add(otherTerms);
    }
    }
    return e;
}

bool isBoundedOscillatoryFactor(const Ctx &c, Expr f)
{
    if (c.kind(f) == NodeKind::Func) {
        const std::string &fn = c.funcName(f);
        return fn == "sin" || fn == "cos";
    }
    if (c.kind(f) == NodeKind::Pow &&
        c.kind(c.child(f, 0)) == NodeKind::Func &&
        c.kind(c.child(f, 1)) == NodeKind::Number &&
        c.numberValue(c.child(f, 1)).signum() > 0) {
        const std::string &fn = c.funcName(c.child(f, 0));
        return fn == "sin" || fn == "cos";
    }
    return false;
}

LimitResult limitDepth(Ctx &c, Expr f, Expr var, Expr x0, Budget *budget,
                       int depth, bool positiveT = false)
{
    LimitResult out;
    if (!checkSeriesBudget(c, budget)) {
        out.reason = budget->status() == BudgetStatus::StepExhausted
                         ? "step budget exhausted"
                         : "arena byte budget exhausted";
        return out;
    }
    if (depth > 6) {
        out.reason = "maximum L'Hopital depth exceeded";
        return out;
    }

    // 1. Truncated Laurent series around t = var - x0.
    for (int pad : {8, 16}) {
        Laurent s;
        if (computeLaurent(c, f, var, x0, pad, budget, s, positiveT)) {
            if (!s.coeffs.empty() && s.val < 0) {
                out.status = LimitResult::Status::Divergent;
                out.poleOrder = -s.val;
                out.reason = "pole at limit point";
                return out;
            }
            if (s.maxDeg >= 0) {
                out.status = LimitResult::Status::Proved;
                out.value = coeffAt(c, s, 0);
                return out;
            }
        }
        if (budget && !budget->ok()) {
            out.reason = budget->status() == BudgetStatus::StepExhausted
                             ? "step budget exhausted"
                             : "arena byte budget exhausted";
            return out;
        }
    }

    // 2. Direct safe substitution when f is continuous at x0.
    const Expr direct = safeSubsAndFold(c, f, var, x0);
    if (!direct.isNull()) {
        out.status = LimitResult::Status::Proved;
        out.value = direct;
        return out;
    }

    // 2b. Direct singularity / asymptotic checks for Pow and Func(log/exp).
    if (c.kind(f) == NodeKind::Pow &&
        c.kind(c.child(f, 1)) == NodeKind::Number) {
        const Expr b = c.child(f, 0);
        const Rational &re = c.numberValue(c.child(f, 1));
        const LimitResult bLim =
            limitDepth(c, b, var, x0, budget, depth + 1, positiveT);
        if (re.signum() < 0) {
            if (bLim.proved() && isZeroCoeff(c, bLim.value)) {
                out.status = LimitResult::Status::Divergent;
                out.poleOrder = 1;
                out.reason = "algebraic pole at limit point";
                return out;
            }
            if (bLim.status == LimitResult::Status::Divergent) {
                out.status = LimitResult::Status::Proved;
                out.value = c.zero();
                return out;
            }
        } else if (re.signum() > 0 &&
                   bLim.status == LimitResult::Status::Divergent) {
            out.status = LimitResult::Status::Divergent;
            out.poleOrder = 1;
            out.reason = "divergent power at limit point";
            return out;
        }
    }
    if (c.kind(f) == NodeKind::Func) {
        const std::string &fn = c.funcName(f);
        const Expr arg = c.child(f, 0);
        if (fn == "log" || fn == "Ei" || fn == "Ci") {
            const LimitResult argLim =
                limitDepth(c, arg, var, x0, budget, depth + 1, positiveT);
            if ((argLim.proved() && isZeroCoeff(c, argLim.value)) ||
                (fn == "log" &&
                 argLim.status == LimitResult::Status::Divergent)) {
                out.status = LimitResult::Status::Divergent;
                out.poleOrder = 1;
                out.reason = "logarithmic singularity at limit point";
                return out;
            }
        } else if (fn == "li") {
            const LimitResult argLim =
                limitDepth(c, arg, var, x0, budget, depth + 1, positiveT);
            if ((argLim.proved() &&
                 isZeroCoeff(
                     c, c.add({argLim.value, c.number(std::int64_t{-1})}))) ||
                argLim.status == LimitResult::Status::Divergent) {
                out.status = LimitResult::Status::Divergent;
                out.poleOrder = 1;
                out.reason = "logarithmic integral singularity at limit point";
                return out;
            }
        }
        if ((fn == "exp" || fn == "Ei" || fn == "erfi") && positiveT) {
            Laurent argS;
            if (computeLaurent(c, arg, var, x0, 4, budget, argS, positiveT) &&
                !argS.coeffs.empty() && argS.val < 0) {
                const int s = exprSign(c, argS.coeffs.front());
                if (s > 0 || (fn == "erfi" && s != 0)) {
                    out.status = LimitResult::Status::Divergent;
                    out.poleOrder = -argS.val;
                    out.reason = "essential exponential growth at limit point";
                    return out;
                }
            }
        }
    }

    // 3. Decompose Mul into bounded oscillatory factors (squeeze theorem) or
    //    numerator / denominator / 0 * log(...) indeterminate forms (L'Hopital).
    if (c.kind(f) == NodeKind::Mul) {
        std::vector<Expr> boundedFactors;
        std::vector<Expr> nonBoundedFactors;
        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            const Expr ch = c.child(f, i);
            if (isBoundedOscillatoryFactor(c, ch))
                boundedFactors.push_back(ch);
            else
                nonBoundedFactors.push_back(ch);
        }
        if (!boundedFactors.empty() && !nonBoundedFactors.empty()) {
            const LimitResult restLim = limitDepth(
                c, c.mul(nonBoundedFactors), var, x0, budget, depth + 1,
                positiveT);
            if (restLim.proved() && isZeroCoeff(c, restLim.value)) {
                out.status = LimitResult::Status::Proved;
                out.value = c.zero();
                return out;
            }
        }

        std::vector<Expr> numFactors;
        std::vector<Expr> denFactors;
        std::vector<Expr> logFactors;
        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            const Expr ch = c.child(f, i);
            if (c.kind(ch) == NodeKind::Pow &&
                c.kind(c.child(ch, 1)) == NodeKind::Number &&
                c.numberValue(c.child(ch, 1)).signum() < 0) {
                denFactors.push_back(
                    c.pow(c.child(ch, 0), c.number(-c.numberValue(c.child(ch, 1)))));
            } else if (c.kind(ch) == NodeKind::Func && c.funcName(ch) == "log") {
                logFactors.push_back(ch);
            } else {
                numFactors.push_back(ch);
            }
        }
        // 0 * log(B) rewrite: A(x) * log(B(x)) = log(B(x)) / (1 / A(x))
        // -> L'Hopital derivative ratio is (B'/B) / (-A'/A^2) = -A^2 * B' / (A' * B).
        if (denFactors.empty() && logFactors.size() == 1 && !numFactors.empty()) {
            const Expr A = c.mul(numFactors);
            const Expr B = c.child(logFactors[0], 0);
            const Expr aAt0 = safeSubsAndFold(c, A, var, x0);
            if (!aAt0.isNull() && isZeroCoeff(c, aAt0)) {
                const Expr dA = c.diff(A, var);
                const Expr dB = c.diff(B, var);
                if (!c.isZero(dA)) {
                    const Expr lhop = c.div(
                        c.neg(c.mul({c.pow(A, c.number(std::int64_t{2})), dB})),
                        c.mul({dA, B}));
                    return limitDepth(c, lhop, var, x0, budget, depth + 1,
                                      positiveT);
                }
            } else if (!aAt0.isNull() && !isZeroCoeff(c, aAt0)) {
                const LimitResult logLim = limitDepth(
                    c, logFactors[0], var, x0, budget, depth + 1, positiveT);
                if (logLim.status == LimitResult::Status::Divergent)
                    return logLim;
            }
        }
        if (!denFactors.empty()) {
            for (const Expr &lf : logFactors)
                numFactors.push_back(lf);
            const Expr N = numFactors.empty() ? c.one() : c.mul(numFactors);
            const Expr D = c.mul(denFactors);
            const Expr nAt0 = safeSubsAndFold(c, N, var, x0);
            const Expr dAt0 = safeSubsAndFold(c, D, var, x0);
            if (!dAt0.isNull() && isZeroCoeff(c, dAt0) && !nAt0.isNull() &&
                !isZeroCoeff(c, nAt0)) {
                out.status = LimitResult::Status::Divergent;
                out.poleOrder = 1;
                out.reason = "non-zero numerator over zero denominator";
                return out;
            }
            const Expr dN = c.diff(N, var);
            const Expr dD = c.diff(D, var);
            if (!c.isZero(dD)) {
                return limitDepth(c, c.div(dN, dD), var, x0, budget, depth + 1,
                                  positiveT);
            }
        }
    }

    // 4. Additive linearity fallback when every summand has a finite Proved
    //    limit, or when exactly one summand diverges and all others are finite.
    if (c.kind(f) == NodeKind::Add) {
        std::vector<Expr> pieceVals;
        pieceVals.reserve(c.childCount(f));
        std::size_t divCount = 0;
        std::size_t unevalCount = 0;
        LimitResult firstDiv;
        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            const LimitResult pi = limitDepth(
                c, c.child(f, i), var, x0, budget, depth + 1, positiveT);
            if (pi.proved()) {
                pieceVals.push_back(pi.value);
            } else if (pi.status == LimitResult::Status::Divergent) {
                ++divCount;
                if (divCount == 1)
                    firstDiv = pi;
            } else {
                ++unevalCount;
                break;
            }
        }
        if (divCount == 0 && unevalCount == 0) {
            out.status = LimitResult::Status::Proved;
            out.value = foldConst(c, c.add(pieceVals));
            return out;
        }
        if (divCount == 1 && unevalCount == 0)
            return firstDiv;
    }

    out.reason = "unable to determine limit";
    return out;
}

bool isSymbolicInfinity(const Ctx &c, Expr e, int &dirOut)
{
    if (e.isNull())
        return false;
    if (c.kind(e) == NodeKind::Symbol) {
        const std::string &nm = c.symbolName(e);
        if (nm == "inf" || nm == "oo" || nm == "infinity") {
            dirOut = +1;
            return true;
        }
    }
    if (c.kind(e) == NodeKind::Mul && c.childCount(e) == 2 &&
        c.kind(c.child(e, 0)) == NodeKind::Number &&
        c.kind(c.child(e, 1)) == NodeKind::Symbol) {
        const std::string &nm = c.symbolName(c.child(e, 1));
        if (nm == "inf" || nm == "oo" || nm == "infinity") {
            const int s = c.numberValue(c.child(e, 0)).signum();
            if (s != 0) {
                dirOut = s > 0 ? +1 : -1;
                return true;
            }
        }
    }
    return false;
}

} // namespace

LimitResult limitOneSided(Ctx &c, Expr f, Expr var, Expr x0, int dir,
                          Budget *budget)
{
    if (f.isNull() || var.isNull() || x0.isNull()) {
        LimitResult out;
        out.reason = "null input expression";
        return out;
    }
    int infDir = 0;
    if (isSymbolicInfinity(c, x0, infDir))
        return limitAtInfinity(c, f, var, infDir, budget);

    const Expr fNorm = combineLogsForLimit(c, c.expand(f));
    const Expr tSym = c.symbol("_t_lim");
    const std::int64_t sgn = dir >= 0 ? std::int64_t{1} : std::int64_t{-1};
    const Expr xSub = c.add({x0, c.mul({c.number(sgn), tSym})});
    const Expr fSub = c.subs(fNorm, var, xSub);
    LimitResult res = limitDepth(c, fSub, tSym, c.zero(), budget, 0, true);
    if (res.status != LimitResult::Status::Unevaluated)
        return res;

    // Puiseux square-root substitution var = x0 + sgn * t^2 (t -> 0+).
    const Expr xPuiseux = c.add(
        {x0, c.mul({c.number(sgn), c.pow(tSym, c.number(std::int64_t{2}))})});
    const Expr fPuiseux = c.subs(fNorm, var, xPuiseux);
    return limitDepth(c, fPuiseux, tSym, c.zero(), budget, 0, true);
}

LimitResult limitAtInfinity(Ctx &c, Expr f, Expr var, int dir, Budget *budget)
{
    if (f.isNull() || var.isNull()) {
        LimitResult out;
        out.reason = "null input expression";
        return out;
    }
    if (!mentionsSymbol(c, f, var)) {
        LimitResult out;
        out.status = LimitResult::Status::Proved;
        out.value = foldConst(c, f);
        return out;
    }
    const Expr fNorm = combineLogsForLimit(c, c.expand(f));
    const Expr tSym = c.symbol("_t_inf");
    const std::int64_t sgn = dir >= 0 ? std::int64_t{1} : std::int64_t{-1};
    const Expr xOfT =
        c.mul({c.number(sgn), c.pow(tSym, c.number(std::int64_t{-1}))});
    const Expr fOfT = c.subs(fNorm, var, xOfT);
    return limitOneSided(c, fOfT, tSym, c.zero(), +1, budget);
}

LimitResult limit(Ctx &c, Expr f, Expr var, Expr x0, Budget *budget)
{
    if (f.isNull() || var.isNull() || x0.isNull()) {
        LimitResult out;
        out.reason = "null input expression";
        return out;
    }
    int infDir = 0;
    if (isSymbolicInfinity(c, x0, infDir))
        return limitAtInfinity(c, f, var, infDir, budget);
    const Expr fNorm = combineLogsForLimit(c, f);
    return limitDepth(c, fNorm, var, x0, budget, 0, false);
}

Expr residue(Ctx &c, Expr f, Expr var, Expr z0, Budget *budget)
{
    if (f.isNull() || var.isNull() || z0.isNull())
        return Expr();
    if (!checkSeriesBudget(c, budget))
        return Expr();

    int infDir = 0;
    if (isSymbolicInfinity(c, z0, infDir)) {
        const Expr tSym = c.symbol("_t_res_inf");
        const Expr fSub = c.subs(f, var, c.pow(tSym, c.number(std::int64_t{-1})));
        const Expr fInf =
            c.neg(c.mul({c.pow(tSym, c.number(std::int64_t{-2})), fSub}));
        return residue(c, fInf, tSym, c.zero(), budget);
    }

    if (!mentionsSymbol(c, f, var))
        return c.zero();

    // 1. Primary path: truncated Laurent expansion around t = var - z0.
    for (int pad : {8, 16, 24}) {
        Laurent s;
        if (computeLaurent(c, f, var, z0, pad, budget, s)) {
            if (s.maxDeg >= -1)
                return c.simplify(coeffAt(c, s, -1));
        }
        if (budget && !budget->ok())
            return Expr();
    }

    // 2. Fallback: pole-order multiplier (var - z0)^m * f(var) for m = 1..5.
    const Expr dz = c.isZero(z0) ? var : c.add({var, c.neg(z0)});
    BigInt fact(1);
    for (int m = 1; m <= 5; ++m) {
        if (!checkSeriesBudget(c, budget))
            return Expr();
        if (m >= 2)
            fact = fact * BigInt(m - 1);
        const Expr gm = c.simplify(
            c.mul({c.pow(dz, c.number(static_cast<std::int64_t>(m))), f}));
        Expr deriv = gm;
        for (int k = 1; k < m; ++k)
            deriv = c.diff(deriv, var);
        const LimitResult lr = limit(c, deriv, var, z0, budget);
        if (lr.proved()) {
            return c.simplify(
                c.mul({c.number(Rational(BigInt(1), fact)), lr.value}));
        }
    }

    return Expr();
}

} // namespace numkit::cas
