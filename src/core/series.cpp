#include <numkit/cas/core/series.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

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
    if (fn == "dilog" || fn == "Li2" || fn == "polylog2") {
        if (isZeroCoeff(c, c0)) {
            Laurent sum = makeConstSeries(c, c.zero(), L);
            Laurent upow = u;
            for (int k = 1; k <= L && !upow.coeffs.empty(); ++k) {
                const Expr coef = c.number(
                    Rational(BigInt(1), BigInt(k) * BigInt(k)));
                sum = addSeries(c, sum, scaleSeries(c, upow, coef));
                if (k + 1 <= L)
                    upow = mulSeries(c, upow, u);
            }
            out = sum;
            return true;
        }
        if (isZeroCoeff(c, c.add({c0, c.number(std::int64_t{-1})})))
            return false;
        const Laurent oneMinusA = addSeries(
            c, makeConstSeries(c, c.one(), L),
            scaleSeries(c, arg, c.number(std::int64_t{-1})));
        Laurent log1mA, invA, intPart;
        if (!evalFuncSeries(c, "log", oneMinusA, log1mA, positiveT) ||
            !invSeries(c, arg, invA))
            return false;
        const Laurent dA = diffSeries(c, arg);
        const Laurent deriv = scaleSeries(
            c, mulSeries(c, mulSeries(c, log1mA, invA), dA),
            c.number(std::int64_t{-1}));
        if (!integrateSeriesZeroConst(c, deriv, intPart))
            return false;
        const Expr f0 = foldConst(c, c.func("dilog", c0));
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
        } else if (fn == "dilog" || fn == "Li2" || fn == "polylog2") {
            const LimitResult argLim =
                limitDepth(c, arg, var, x0, budget, depth + 1, positiveT);
            if (argLim.status == LimitResult::Status::Divergent) {
                out.status = LimitResult::Status::Divergent;
                out.poleOrder = 1;
                out.reason = "dilogarithmic singularity at limit point";
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
        std::vector<std::int64_t> logExps;
        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            const Expr ch = c.child(f, i);
            if (c.kind(ch) == NodeKind::Pow &&
                c.kind(c.child(ch, 1)) == NodeKind::Number &&
                c.numberValue(c.child(ch, 1)).signum() < 0) {
                denFactors.push_back(
                    c.pow(c.child(ch, 0), c.number(-c.numberValue(c.child(ch, 1)))));
            } else if (c.kind(ch) == NodeKind::Func && c.funcName(ch) == "log" &&
                       safeSubsAndFold(c, ch, var, x0).isNull()) {
                logFactors.push_back(ch);
                logExps.push_back(1);
            } else if (c.kind(ch) == NodeKind::Pow &&
                       c.kind(c.child(ch, 0)) == NodeKind::Func &&
                       c.funcName(c.child(ch, 0)) == "log" &&
                       c.kind(c.child(ch, 1)) == NodeKind::Number &&
                       safeSubsAndFold(c, c.child(ch, 0), var, x0).isNull()) {
                const Rational &re = c.numberValue(c.child(ch, 1));
                std::int64_t kExp = 0;
                if (re.den() == BigInt(1) && re.num().fitsInt64(kExp) &&
                    kExp >= 1) {
                    logFactors.push_back(c.child(ch, 0));
                    logExps.push_back(kExp);
                } else {
                    numFactors.push_back(ch);
                }
            } else {
                numFactors.push_back(ch);
            }
        }
        // 0 * log(B)^k rewrite: A(x) * log(B(x))^k = log(B(x))^k / (1 / A(x))
        // -> L'Hopital derivative ratio is -k * A^2 * B' * log(B)^(k-1) / (A' * B).
        if (denFactors.empty() && logFactors.size() == 1 && !numFactors.empty()) {
            const Expr A = c.mul(numFactors);
            const Expr B = c.child(logFactors[0], 0);
            const std::int64_t kExp = logExps[0];
            const Expr aAt0 = safeSubsAndFold(c, A, var, x0);
            if (!aAt0.isNull() && isZeroCoeff(c, aAt0)) {
                const Expr dA = c.diff(A, var);
                const Expr dB = c.diff(B, var);
                if (!c.isZero(dA)) {
                    const Expr logPowM1 =
                        (kExp == 1)
                            ? c.one()
                            : c.pow(logFactors[0], c.number(kExp - 1));
                    const Expr lhop = c.div(
                        c.neg(c.mul({c.number(kExp),
                                     c.pow(A, c.number(std::int64_t{2})), dB,
                                     logPowM1})),
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
            for (std::size_t i = 0; i < logFactors.size(); ++i) {
                numFactors.push_back(
                    logExps[i] == 1
                        ? logFactors[i]
                        : c.pow(logFactors[i], c.number(logExps[i])));
            }
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

// Expand asymptotic dilog(u(t)) (for u(t) -> -infinity as t -> 0+) using
// Euler's inversion identity:
//   dilog(u) -> -dilog(1/u) - pi^2/6 - (1/2)*log(-u)^2,
// and split singular log(v(t)) (for v(t) ~ c0 * t^k with k != 0, c0 > 0) into:
//   log(v(t)) -> log(c0) + k*log(t) + log(v(t) / (c0 * t^k)),
// so canceling log(t) and log(t)^2 singularities cancel algebraically.
Expr expandAsymptoticLogsAndDilog(Ctx &c, Expr e, Expr tSym, Budget *budget,
                                  bool &changedOut)
{
    if (e.isNull() || !mentionsSymbol(c, e, tSym))
        return e;
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Pow:
        return c.pow(expandAsymptoticLogsAndDilog(c, c.child(e, 0), tSym,
                                                  budget, changedOut),
                     expandAsymptoticLogsAndDilog(c, c.child(e, 1), tSym,
                                                  budget, changedOut));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            ch.push_back(expandAsymptoticLogsAndDilog(c, c.child(e, i), tSym,
                                                      budget, changedOut));
        }
        return c.kind(e) == NodeKind::Add ? c.add(ch) : c.mul(ch);
    }
    case NodeKind::Func: {
        const std::string &fn = c.funcName(e);
        const Expr arg = expandAsymptoticLogsAndDilog(c, c.child(e, 0), tSym,
                                                      budget, changedOut);
        if (fn == "dilog" || fn == "Li2" || fn == "polylog2") {
            Laurent s;
            if (computeLaurent(c, arg, tSym, c.zero(), 4, budget, s, true) &&
                !s.coeffs.empty() && s.val < 0 &&
                exprSign(c, s.coeffs.front()) < 0) {
                changedOut = true;
                const Expr invArg =
                    c.simplify(c.pow(arg, c.number(std::int64_t{-1})));
                const Expr negArg = c.simplify(c.neg(arg));
                const Expr logNegArg = expandAsymptoticLogsAndDilog(
                    c, c.func("log", negArg), tSym, budget, changedOut);
                const Expr pi2Over6 = c.mul(
                    {c.number(Rational(std::int64_t{1}, BigInt(6))),
                     c.pow(c.symbol("pi"), c.number(std::int64_t{2}))});
                const Expr halfLogSq = c.mul(
                    {c.number(Rational(std::int64_t{1}, BigInt(2))),
                     c.pow(logNegArg, c.number(std::int64_t{2}))});
                return c.add({c.neg(c.func("dilog", invArg)), c.neg(pi2Over6),
                              c.neg(halfLogSq)});
            }
            return c.func("dilog", arg);
        }
        if (fn == "log" && !(arg == tSym)) {
            Laurent s;
            if (computeLaurent(c, arg, tSym, c.zero(), 4, budget, s, true) &&
                !s.coeffs.empty() && s.val != 0 &&
                exprSign(c, s.coeffs.front()) > 0) {
                const int k = s.val;
                const Expr c0 = s.coeffs.front();
                const Expr uTilde = c.simplify(c.mul(
                    {arg, c.pow(c0, c.number(std::int64_t{-1})),
                     c.pow(tSym, c.number(static_cast<std::int64_t>(-k)))}));
                const Expr uAt0 = safeSubsAndFold(c, uTilde, tSym, c.zero());
                if (!uAt0.isNull() &&
                    isZeroCoeff(c, c.add({uAt0, c.number(std::int64_t{-1})}))) {
                    changedOut = true;
                    const Expr logC0 = c.simplify(c.func("log", c0));
                    const Expr kLogT = c.mul(
                        {c.number(static_cast<std::int64_t>(k)),
                         c.func("log", tSym)});
                    const Expr logUTilde =
                        isZeroCoeff(
                            c, c.add({uTilde, c.number(std::int64_t{-1})}))
                            ? c.zero()
                            : c.func("log", uTilde);
                    return c.add({logC0, kLogT, logUTilde});
                }
            }
        }
        return c.func(fn, arg);
    }
    }
    return e;
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
    Expr fSub = c.subs(fNorm, var, xSub);
    bool changedAsym = false;
    const Expr fAsym =
        expandAsymptoticLogsAndDilog(c, fSub, tSym, budget, changedAsym);
    if (changedAsym && !fAsym.isNull())
        fSub = combineLogsForLimit(c, c.expand(fAsym));
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

namespace {

Rational binomRational(int n, int k)
{
    if (k < 0 || k > n)
        return Rational(std::int64_t{0});
    if (k == 0 || k == n)
        return Rational(std::int64_t{1});
    if (k > n - k)
        k = n - k;
    BigInt num(1);
    BigInt den(1);
    for (int i = 1; i <= k; ++i) {
        num = num * BigInt(n - k + i);
        den = den * BigInt(i);
    }
    return Rational(num, den);
}

// Compute classical Bernoulli numbers B_0 = 1, B_1 = -1/2, B_2 = 1/6, B_3 = 0, ...
std::vector<Rational> bernoulliNumbers(int maxN)
{
    std::vector<Rational> B(static_cast<std::size_t>(maxN + 1),
                            Rational(std::int64_t{0}));
    B[0] = Rational(std::int64_t{1});
    for (int m = 1; m <= maxN; ++m) {
        if (m >= 3 && (m % 2 == 1)) {
            B[static_cast<std::size_t>(m)] = Rational(std::int64_t{0});
            continue;
        }
        Rational sum(std::int64_t{0});
        for (int j = 0; j < m; ++j) {
            if (!B[static_cast<std::size_t>(j)].isZero())
                sum = sum + binomRational(m + 1, j) * B[static_cast<std::size_t>(j)];
        }
        B[static_cast<std::size_t>(m)] =
            -sum / Rational(static_cast<std::int64_t>(m + 1));
    }
    return B;
}

// Euler's exact formula for zeta(2*m) (m >= 1):
//   zeta(2*m) = (-1)^(m-1) * 2^(2*m - 1) * B_{2m} / (2*m)! * pi^(2*m).
Expr eulerZetaEven(Ctx &c, int twoM)
{
    const int m = twoM / 2;
    const std::vector<Rational> B = bernoulliNumbers(twoM);
    Rational bVal = B[static_cast<std::size_t>(twoM)];
    if (bVal.signum() < 0)
        bVal = -bVal;
    BigInt fact(1);
    for (int i = 2; i <= twoM; ++i)
        fact = fact * BigInt(i);
    const BigInt pow2 = BigInt(1) << static_cast<std::size_t>(twoM - 1);
    const Rational coef =
        bVal * Rational(pow2, fact);
    return c.mul({c.number(coef),
                  c.pow(c.symbol("pi"),
                        c.number(static_cast<std::int64_t>(twoM)))});
}

bool extractPolyCoeffsInVar(Ctx &c, Expr e, Expr var, int maxDeg,
                            std::vector<Expr> &coeffs)
{
    const Expr expanded = c.expand(e);
    std::vector<Expr> terms;
    if (c.kind(expanded) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(expanded); ++i)
            terms.push_back(c.child(expanded, i));
    } else {
        terms.push_back(expanded);
    }

    coeffs.assign(1, c.zero());
    for (const Expr &t : terms) {
        if (!mentionsSymbol(c, t, var)) {
            coeffs[0] = c.add({coeffs[0], t});
            continue;
        }
        std::vector<Expr> facs;
        if (c.kind(t) == NodeKind::Mul) {
            for (std::size_t i = 0; i < c.childCount(t); ++i)
                facs.push_back(c.child(t, i));
        } else {
            facs.push_back(t);
        }
        int deg = 0;
        std::vector<Expr> cFacs;
        for (const Expr &f : facs) {
            if (!mentionsSymbol(c, f, var)) {
                cFacs.push_back(f);
            } else if (f == var) {
                deg += 1;
            } else if (c.kind(f) == NodeKind::Pow && c.child(f, 0) == var &&
                       c.kind(c.child(f, 1)) == NodeKind::Number) {
                const Rational &re = c.numberValue(c.child(f, 1));
                std::int64_t k = 0;
                if (!(re.den() == BigInt(1)) || !re.num().fitsInt64(k) ||
                    k < 0 || deg + k > maxDeg) {
                    return false;
                }
                deg += static_cast<int>(k);
            } else {
                return false;
            }
        }
        if (deg > maxDeg)
            return false;
        if (static_cast<std::size_t>(deg) >= coeffs.size())
            coeffs.resize(static_cast<std::size_t>(deg + 1), c.zero());
        const Expr cf = cFacs.empty() ? c.one() : c.mul(cFacs);
        coeffs[static_cast<std::size_t>(deg)] =
            c.add({coeffs[static_cast<std::size_t>(deg)], cf});
    }
    for (Expr &cf : coeffs)
        cf = c.simplify(cf);
    while (coeffs.size() > 1 && c.isZero(coeffs.back()))
        coeffs.pop_back();
    return true;
}

Expr evalSymbolicPolyInVar(Ctx &c, const std::vector<Expr> &coeffs, Expr var)
{
    std::vector<Expr> terms;
    for (std::size_t i = 0; i < coeffs.size(); ++i) {
        if (c.isZero(coeffs[i]))
            continue;
        if (i == 0) {
            terms.push_back(coeffs[0]);
        } else if (i == 1) {
            terms.push_back(c.mul({coeffs[1], var}));
        } else {
            terms.push_back(c.mul(
                {coeffs[i],
                 c.pow(var, c.number(static_cast<std::int64_t>(i)))}));
        }
    }
    return terms.empty() ? c.zero() : c.add(terms);
}

Expr expandShiftPowers(Ctx &c, Expr e, Expr var)
{
    if (e.isNull())
        return Expr();
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Pow: {
        const Expr b = expandShiftPowers(c, c.child(e, 0), var);
        const Expr ex = c.expand(expandShiftPowers(c, c.child(e, 1), var));
        if (!mentionsSymbol(c, b, var) && c.kind(ex) == NodeKind::Add) {
            std::vector<Expr> varTerms, constTerms;
            for (std::size_t i = 0; i < c.childCount(ex); ++i) {
                const Expr ch = c.child(ex, i);
                if (mentionsSymbol(c, ch, var))
                    varTerms.push_back(ch);
                else
                    constTerms.push_back(ch);
            }
            if (!varTerms.empty() && !constTerms.empty()) {
                return c.mul({c.pow(b, c.add(constTerms)),
                              c.pow(b, c.add(varTerms))});
            }
        }
        return c.pow(b, ex);
    }
    case NodeKind::Func: {
        const std::string &fn = c.funcName(e);
        const Expr arg = c.expand(expandShiftPowers(c, c.child(e, 0), var));
        if (fn == "exp" && c.kind(arg) == NodeKind::Add) {
            std::vector<Expr> varTerms, constTerms;
            for (std::size_t i = 0; i < c.childCount(arg); ++i) {
                const Expr ch = c.child(arg, i);
                if (mentionsSymbol(c, ch, var))
                    varTerms.push_back(ch);
                else
                    constTerms.push_back(ch);
            }
            if (!varTerms.empty() && !constTerms.empty()) {
                return c.mul({c.func("exp", c.add(constTerms)),
                              c.func("exp", c.add(varTerms))});
            }
        }
        return c.func(fn, arg);
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            ch.push_back(expandShiftPowers(c, c.child(e, i), var));
        return c.kind(e) == NodeKind::Add ? c.add(ch) : c.mul(ch);
    }
    }
    return e;
}

bool certifyDiscreteAntidiff(Ctx &c, Expr G, Expr f, Expr var)
{
    if (G.isNull() || f.isNull())
        return false;
    const Expr gNext = c.subs(G, var, c.add({var, c.one()}));
    const Expr raw = c.add({gNext, c.neg(G), c.neg(f)});
    if (c.isZero(raw))
        return true;
    const Expr simp = c.simplify(raw);
    if (!simp.isNull() && c.isZero(simp))
        return true;
    const Expr expSimp =
        c.simplify(c.expand(expandShiftPowers(c, raw, var)));
    return !expSimp.isNull() && c.isZero(expSimp);
}

// Faulhaber-Bernoulli polynomial antidifference:
//   Delta(G(var)) == P(var) where P(var) = sum_{m=0}^d p_m * var^m.
Expr polyDiscreteAntidiff(Ctx &c, const std::vector<Expr> &pCoeffs, Expr var)
{
    const int d = static_cast<int>(pCoeffs.size()) - 1;
    if (d < 0)
        return c.zero();
    const std::vector<Rational> B = bernoulliNumbers(d + 1);
    std::vector<Expr> terms;
    for (int m = 0; m <= d; ++m) {
        const Expr &pm = pCoeffs[static_cast<std::size_t>(m)];
        if (c.isZero(pm))
            continue;
        std::vector<Expr> mTerms;
        for (int j = 0; j <= m; ++j) {
            if (B[static_cast<std::size_t>(j)].isZero())
                continue;
            const Rational coef =
                (binomRational(m + 1, j) * B[static_cast<std::size_t>(j)]) /
                Rational(static_cast<std::int64_t>(m + 1));
            const int degK = m + 1 - j;
            const Expr kPow =
                (degK == 1)
                    ? var
                    : c.pow(var, c.number(static_cast<std::int64_t>(degK)));
            mTerms.push_back(c.mul({c.number(coef), kPow}));
        }
        if (!mTerms.empty())
            terms.push_back(c.mul({pm, c.add(mTerms)}));
    }
    return terms.empty() ? c.zero() : c.simplify(c.add(terms));
}

bool discreteAntidiff(Ctx &c, Expr f, Expr var, Budget *budget, Expr &gOut,
                      Expr *geomRatioOut = nullptr)
{
    if (!checkSeriesBudget(c, budget))
        return false;
    if (!mentionsSymbol(c, f, var)) {
        gOut = c.mul({f, var});
        return true;
    }

    // 1. Polynomial in `var` (Faulhaber-Bernoulli).
    std::vector<Expr> pCoeffs;
    if (extractPolyCoeffsInVar(c, f, var, 16, pCoeffs)) {
        const Expr G = polyDiscreteAntidiff(c, pCoeffs, var);
        if (certifyDiscreteAntidiff(c, G, f, var)) {
            gOut = G;
            return true;
        }
    }

    // 2. Geometric and arithmetico-geometric terms: P(var) * R(var)
    //    where q = R(var + 1) / R(var) is independent of `var` and q != 1.
    std::vector<Expr> factors;
    if (c.kind(f) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(f); ++i)
            factors.push_back(c.child(f, i));
    } else {
        factors.push_back(f);
    }
    std::vector<Expr> geomFacs, otherFacs;
    for (const Expr &fac : factors) {
        bool isGeom = false;
        if (c.kind(fac) == NodeKind::Pow &&
            !mentionsSymbol(c, c.child(fac, 0), var) &&
            mentionsSymbol(c, c.child(fac, 1), var)) {
            std::vector<Expr> eCoeffs;
            if (extractPolyCoeffsInVar(c, c.child(fac, 1), var, 1, eCoeffs) &&
                eCoeffs.size() == 2 && !c.isZero(eCoeffs[1])) {
                isGeom = true;
            }
        } else if (c.kind(fac) == NodeKind::Func &&
                   c.funcName(fac) == "exp" &&
                   mentionsSymbol(c, c.child(fac, 0), var)) {
            std::vector<Expr> eCoeffs;
            if (extractPolyCoeffsInVar(c, c.child(fac, 0), var, 1, eCoeffs) &&
                eCoeffs.size() == 2 && !c.isZero(eCoeffs[1])) {
                isGeom = true;
            }
        }
        if (isGeom)
            geomFacs.push_back(fac);
        else
            otherFacs.push_back(fac);
    }
    if (!geomFacs.empty()) {
        const Expr R = geomFacs.size() == 1 ? geomFacs[0] : c.mul(geomFacs);
        const Expr rest = otherFacs.empty() ? c.one() : c.mul(otherFacs);
        const Expr rNext = expandShiftPowers(
            c, c.subs(R, var, c.add({var, c.one()})), var);
        const Expr q = c.simplify(c.div(rNext, R));
        std::vector<Expr> polyP;
        if (!q.isNull() && !mentionsSymbol(c, q, var) &&
            extractPolyCoeffsInVar(c, rest, var, 10, polyP)) {
            const Expr qMinus1 =
                c.simplify(c.add({q, c.number(std::int64_t{-1})}));
            if (c.isZero(qMinus1)) {
                const Expr G = polyDiscreteAntidiff(c, polyP, var);
                if (certifyDiscreteAntidiff(c, G, f, var)) {
                    gOut = G;
                    return true;
                }
            } else {
                const int d = static_cast<int>(polyP.size()) - 1;
                std::vector<Expr> qCoeffs(static_cast<std::size_t>(d + 1),
                                          c.zero());
                for (int m = d; m >= 0; --m) {
                    std::vector<Expr> upperTerms;
                    for (int j = m + 1; j <= d; ++j) {
                        const Expr &qj = qCoeffs[static_cast<std::size_t>(j)];
                        if (!c.isZero(qj)) {
                            upperTerms.push_back(
                                c.mul({c.number(binomRational(j, m)), qj}));
                        }
                    }
                    Expr rhs = polyP[static_cast<std::size_t>(m)];
                    if (!upperTerms.empty()) {
                        rhs = c.add(
                            {rhs, c.neg(c.mul({q, c.add(upperTerms)}))});
                    }
                    qCoeffs[static_cast<std::size_t>(m)] =
                        c.simplify(c.div(rhs, qMinus1));
                }
                const Expr G =
                    c.mul({evalSymbolicPolyInVar(c, qCoeffs, var), R});
                if (certifyDiscreteAntidiff(c, G, f, var)) {
                    gOut = G;
                    if (geomRatioOut)
                        *geomRatioOut = q;
                    return true;
                }
            }
        }
    }

    // 3. Rational telescoping over Q(var) via partial fractions and Z-shift cosets.
    UPoly N, D;
    if (toRational(c, f, var, N, D) && !D.isZero() && D.deg() >= 1) {
        const UPoly gnd = UPoly::gcd(N, D);
        if (gnd.deg() >= 1) {
            UPoly qN, rN, qD, rD;
            UPoly::divMod(N, gnd, qN, rN);
            UPoly::divMod(D, gnd, qD, rD);
            N = qN;
            D = qD;
        }
        const Rational dLc = D.lc();
        UPoly dMonic = D;
        dMonic.makeMonic();
        N = N * UPoly({Rational(std::int64_t{1}) / dLc});
        UPoly qPoly, rPoly;
        UPoly::divMod(N, dMonic, qPoly, rPoly);

        std::vector<UPoly> irreds = factorOverQ(dMonic, budget);
        struct LinFactor
        {
            Rational root;
            UPoly lin;
            int mult = 0;
            UPoly linPow;
        };
        std::vector<LinFactor> lfs;
        bool allLinear = !(budget && !budget->ok());
        for (const UPoly &ir : irreds) {
            if (ir.deg() != 1) {
                allLinear = false;
                break;
            }
            const Rational rt = -ir.coeff(0) / ir.coeff(1);
            bool found = false;
            for (auto &lf : lfs) {
                if (lf.root == rt) {
                    lf.mult += 1;
                    lf.linPow = lf.linPow * ir;
                    found = true;
                    break;
                }
            }
            if (!found)
                lfs.push_back(LinFactor{rt, ir, 1, ir});
        }
        if (allLinear && !lfs.empty()) {
            struct PoleTerm
            {
                Rational root;
                int order = 0;
                Rational coeff;
            };
            std::vector<PoleTerm> poleTerms;
            for (std::size_t j = 0; j < lfs.size(); ++j) {
                UPoly mj({Rational(std::int64_t{1})});
                for (std::size_t i = 0; i < lfs.size(); ++i) {
                    if (i != j)
                        mj = mj * lfs[i].linPow;
                }
                const UPoly invMj =
                    UPoly::invMod(mj % lfs[j].linPow, lfs[j].linPow);
                UPoly cur = (rPoly * invMj) % lfs[j].linPow;
                for (int p = lfs[j].mult; p >= 1 && !cur.isZero(); --p) {
                    UPoly quot, rem;
                    UPoly::divMod(cur, lfs[j].lin, quot, rem);
                    cur = quot;
                    if (!rem.isZero() && !rem.coeff(0).isZero()) {
                        poleTerms.push_back(
                            PoleTerm{lfs[j].root, p, rem.coeff(0)});
                    }
                }
            }

            // Group by (order, root mod Z).
            std::vector<bool> used(poleTerms.size(), false);
            std::vector<Expr> gPieces;
            if (!qPoly.isZero()) {
                std::vector<Expr> qCoeffs;
                for (int i = 0; i <= qPoly.deg(); ++i)
                    qCoeffs.push_back(c.number(qPoly.coeff(i)));
                gPieces.push_back(polyDiscreteAntidiff(c, qCoeffs, var));
            }
            bool canTelescope = true;
            for (std::size_t i = 0; i < poleTerms.size() && canTelescope; ++i) {
                if (used[i])
                    continue;
                std::vector<std::size_t> group{i};
                used[i] = true;
                Rational sumCoeff = poleTerms[i].coeff;
                Rational maxRoot = poleTerms[i].root;
                for (std::size_t j = i + 1; j < poleTerms.size(); ++j) {
                    if (used[j] || poleTerms[j].order != poleTerms[i].order)
                        continue;
                    const Rational diffR =
                        poleTerms[i].root - poleTerms[j].root;
                    if (diffR.den() == BigInt(1)) {
                        used[j] = true;
                        group.push_back(j);
                        sumCoeff = sumCoeff + poleTerms[j].coeff;
                        if (maxRoot < poleTerms[j].root)
                            maxRoot = poleTerms[j].root;
                    }
                }
                if (!sumCoeff.isZero()) {
                    canTelescope = false;
                    break;
                }
                const int p = poleTerms[i].order;
                const Expr baseL =
                    maxRoot.isZero()
                        ? var
                        : c.add({var, c.number(-maxRoot)});
                for (std::size_t idx : group) {
                    const Rational shiftRat = maxRoot - poleTerms[idx].root;
                    std::int64_t s = 0;
                    if (!shiftRat.num().fitsInt64(s) || s < 0 || s > 64) {
                        canTelescope = false;
                        break;
                    }
                    if (s == 0)
                        continue;
                    std::vector<Expr> shiftSum;
                    for (std::int64_t m = 0; m < s; ++m) {
                        const Expr denomBase =
                            (m == 0) ? baseL
                                     : c.add({baseL, c.number(m)});
                        shiftSum.push_back(c.pow(
                            denomBase,
                            c.number(static_cast<std::int64_t>(-p))));
                    }
                    gPieces.push_back(c.mul(
                        {c.number(poleTerms[idx].coeff), c.add(shiftSum)}));
                }
            }
            if (canTelescope) {
                const Expr G =
                    gPieces.empty() ? c.zero() : c.simplify(c.add(gPieces));
                if (certifyDiscreteAntidiff(c, G, f, var)) {
                    gOut = G;
                    return true;
                }
            }
        }
    }

    // 4. Logarithmic telescoping: c0 * log((a*var + b1) / (a*var + b0))
    //    where (b1 - b0)/a = s is a non-zero integer.
    {
        Expr logArg;
        std::vector<Expr> cFacs;
        for (const Expr &fac : factors) {
            if (logArg.isNull() && c.kind(fac) == NodeKind::Func &&
                c.funcName(fac) == "log") {
                logArg = c.child(fac, 0);
            } else if (!mentionsSymbol(c, fac, var)) {
                cFacs.push_back(fac);
            } else {
                logArg = Expr();
                break;
            }
        }
        UPoly lN, lD;
        if (!logArg.isNull() && toRational(c, logArg, var, lN, lD) &&
            lN.deg() == 1 && lD.deg() == 1 && lN.coeff(1) == lD.coeff(1)) {
            const Rational aRat = lD.coeff(1);
            const Rational sRat = (lN.coeff(0) - lD.coeff(0)) / aRat;
            std::int64_t s = 0;
            if (sRat.den() == BigInt(1) && sRat.num().fitsInt64(s) && s != 0 &&
                std::abs(s) <= 32) {
                const Expr coef = cFacs.empty() ? c.one() : c.mul(cFacs);
                const UPoly &basePoly = (s > 0) ? lD : lN;
                const Expr baseExpr = toExpr(c, basePoly, var);
                const std::int64_t absS = std::abs(s);
                std::vector<Expr> logTerms;
                for (std::int64_t m = 0; m < absS; ++m) {
                    const Expr shifted =
                        (m == 0)
                            ? baseExpr
                            : c.add({baseExpr,
                                     c.number(aRat * Rational(m))});
                    logTerms.push_back(c.func("log", shifted));
                }
                const Expr G = c.mul(
                    {coef,
                     c.number(s > 0 ? std::int64_t{1} : std::int64_t{-1}),
                     c.add(logTerms)});
                if (certifyDiscreteAntidiff(c, G, f, var)) {
                    gOut = G;
                    return true;
                }
            }
        }
    }

    // 5. Additive linearity over expanded sum.
    const Expr fExp = c.expand(f);
    if (c.kind(fExp) == NodeKind::Add) {
        std::vector<Expr> pieces;
        pieces.reserve(c.childCount(fExp));
        for (std::size_t i = 0; i < c.childCount(fExp); ++i) {
            Expr gi;
            if (!discreteAntidiff(c, c.child(fExp, i), var, budget, gi))
                return false;
            pieces.push_back(gi);
        }
        const Expr G = c.simplify(c.add(pieces));
        if (certifyDiscreteAntidiff(c, G, f, var)) {
            gOut = G;
            return true;
        }
    }

    return false;
}

} // namespace

SymSumResult symsum(Ctx &c, Expr f, Expr var, Expr a, Expr b, Budget *budget)
{
    SymSumResult out;
    if (f.isNull() || var.isNull() || a.isNull() || b.isNull()) {
        out.reason = "null input expression";
        return out;
    }
    if (!checkSeriesBudget(c, budget)) {
        out.reason = budget->status() == BudgetStatus::StepExhausted
                         ? "step budget exhausted"
                         : "arena byte budget exhausted";
        return out;
    }

    int aInfDir = 0, bInfDir = 0;
    const bool aIsInf = isSymbolicInfinity(c, a, aInfDir);
    const bool bIsInf = isSymbolicInfinity(c, b, bInfDir);
    if (aIsInf) {
        out.reason = "infinite lower summation bound is not supported";
        return out;
    }

    // Case 1: Finite summation bounds [a, b].
    if (!bIsInf) {
        Rational spanRat;
        std::int64_t spanInt = 0;
        const bool hasIntSpan =
            c.evalExact(c.simplify(c.add({b, c.neg(a)})), {}, spanRat) &&
            spanRat.den() == BigInt(1) && spanRat.num().fitsInt64(spanInt);
        if (hasIntSpan) {
            if (spanInt == -1) {
                out.value = c.zero();
                out.status = SymSumResult::Status::ProvedSymbolic;
                return out;
            }
            if (spanInt < -1) {
                out.reason = "upper summation bound is less than a - 1";
                return out;
            }
            if (spanInt <= 128) {
                for (std::int64_t j = 0; j <= spanInt; ++j) {
                    const Expr kVal = c.add({a, c.number(j)});
                    if (safeSubsAndFold(c, f, var, kVal).isNull()) {
                        out.status = SymSumResult::Status::Divergent;
                        out.reason = "summand pole on summation range";
                        return out;
                    }
                }
            }
        }

        Expr G;
        if (discreteAntidiff(c, f, var, budget, G)) {
            const Expr gB1 =
                safeSubsAndFold(c, G, var, c.add({b, c.one()}));
            const Expr gA = safeSubsAndFold(c, G, var, a);
            if (!gB1.isNull() && !gA.isNull()) {
                out.antidiff = G;
                out.value = c.simplify(c.add({gB1, c.neg(gA)}));
                out.status = SymSumResult::Status::ProvedSymbolic;
                return out;
            }
        }

        // Direct finite evaluation fallback for concrete integer spans <= 128.
        if (hasIntSpan && spanInt >= 0 && spanInt <= 128) {
            std::vector<Expr> terms;
            terms.reserve(static_cast<std::size_t>(spanInt + 1));
            for (std::int64_t j = 0; j <= spanInt; ++j) {
                const Expr term =
                    safeSubsAndFold(c, f, var, c.add({a, c.number(j)}));
                if (term.isNull()) {
                    out.status = SymSumResult::Status::Divergent;
                    out.reason = "summand pole on summation range";
                    return out;
                }
                terms.push_back(term);
            }
            out.value = c.simplify(c.add(terms));
            out.status = SymSumResult::Status::ProvedSymbolic;
            return out;
        }

        out.reason = "no closed-form discrete antidifference found";
        return out;
    }

    // Case 2: Infinite series sum_{var = a}^{+inf} f(var).
    if (bInfDir < 0) {
        out.reason = "negative infinity upper bound is not supported";
        return out;
    }
    if (!mentionsSymbol(c, f, var)) {
        if (isZeroCoeff(c, f)) {
            out.value = c.zero();
            out.status = SymSumResult::Status::ProvedSymbolic;
            return out;
        }
        out.status = SymSumResult::Status::Divergent;
        out.reason = "non-zero constant summand over infinite range";
        return out;
    }

    // 2a. Discrete antidifference G(var) with lim_{var -> +inf} G(var).
    Expr G, geomRatio;
    if (discreteAntidiff(c, f, var, budget, G, &geomRatio)) {
        const Expr gA = safeSubsAndFold(c, G, var, a);
        if (gA.isNull()) {
            out.status = SymSumResult::Status::Divergent;
            out.reason = "summand pole at lower bound";
            return out;
        }
        if (!geomRatio.isNull()) {
            double qVal = 0.0;
            if (c.evalDouble(geomRatio, {}, qVal)) {
                if (std::abs(qVal) < 1.0 - 1e-12) {
                    out.antidiff = G;
                    out.value = c.simplify(c.neg(gA));
                    out.status = SymSumResult::Status::ProvedSymbolic;
                    return out;
                }
                out.status = SymSumResult::Status::Divergent;
                out.reason = "geometric ratio |q| >= 1";
                return out;
            }
        }
        const LimitResult limInf = limitAtInfinity(c, G, var, +1, budget);
        if (limInf.status == LimitResult::Status::Divergent) {
            out.status = SymSumResult::Status::Divergent;
            out.reason = "divergent partial sums at infinity";
            return out;
        }
        if (limInf.proved()) {
            out.antidiff = G;
            out.value = c.simplify(c.add({limInf.value, c.neg(gA)}));
            out.status = SymSumResult::Status::ProvedSymbolic;
            return out;
        }
    }

    // Check if lower bound `a` is an integer a0.
    Rational aRat;
    std::int64_t a0 = 0;
    const bool hasIntA =
        c.evalExact(a, {}, aRat) && aRat.den() == BigInt(1) &&
        aRat.num().fitsInt64(a0);

    // 2b. Rational infinite series sum_{k = a0}^{inf} N(k)/D(k) over Q(k):
    //     Euler-Riemann zeta(2*m) and mixed telescoping + zeta(2*m).
    UPoly N, D;
    if (hasIntA && toRational(c, f, var, N, D) && !D.isZero() && D.deg() >= 1) {
        if (N.isZero()) {
            out.value = c.zero();
            out.status = SymSumResult::Status::ProvedSymbolic;
            return out;
        }
        const UPoly gnd = UPoly::gcd(N, D);
        if (gnd.deg() >= 1) {
            UPoly qN, rN, qD, rD;
            UPoly::divMod(N, gnd, qN, rN);
            UPoly::divMod(D, gnd, qD, rD);
            N = qN;
            D = qD;
        }
        if (N.deg() >= D.deg() - 1) {
            // Since discreteAntidiff already checked whether p = 1 residues
            // cancel, deg(N) >= deg(D) - 1 here guarantees divergence.
            out.status = SymSumResult::Status::Divergent;
            out.reason = "rational series of degree >= -1 does not converge";
            return out;
        }
        const Rational dLc = D.lc();
        UPoly dMonic = D;
        dMonic.makeMonic();
        N = N * UPoly({Rational(std::int64_t{1}) / dLc});
        std::vector<UPoly> irreds = factorOverQ(dMonic, budget);
        struct LinFactor
        {
            Rational root;
            UPoly lin;
            int mult = 0;
            UPoly linPow;
        };
        std::vector<LinFactor> lfs;
        bool allLinear = !(budget && !budget->ok());
        for (const UPoly &ir : irreds) {
            if (ir.deg() != 1) {
                allLinear = false;
                break;
            }
            const Rational rt = -ir.coeff(0) / ir.coeff(1);
            std::int64_t rtInt = 0;
            if (rt.den() == BigInt(1) && rt.num().fitsInt64(rtInt) &&
                rtInt >= a0) {
                out.status = SymSumResult::Status::Divergent;
                out.reason = "pole of rational summand on summation range";
                return out;
            }
            bool found = false;
            for (auto &lf : lfs) {
                if (lf.root == rt) {
                    lf.mult += 1;
                    lf.linPow = lf.linPow * ir;
                    found = true;
                    break;
                }
            }
            if (!found)
                lfs.push_back(LinFactor{rt, ir, 1, ir});
        }
        if (allLinear && !lfs.empty()) {
            struct PoleTerm
            {
                Rational root;
                int order = 0;
                Rational coeff;
            };
            std::vector<PoleTerm> poleTerms;
            for (std::size_t j = 0; j < lfs.size(); ++j) {
                UPoly mj({Rational(std::int64_t{1})});
                for (std::size_t i = 0; i < lfs.size(); ++i) {
                    if (i != j)
                        mj = mj * lfs[i].linPow;
                }
                const UPoly invMj =
                    UPoly::invMod(mj % lfs[j].linPow, lfs[j].linPow);
                UPoly cur = (N * invMj) % lfs[j].linPow;
                for (int p = lfs[j].mult; p >= 1 && !cur.isZero(); --p) {
                    UPoly quot, rem;
                    UPoly::divMod(cur, lfs[j].lin, quot, rem);
                    cur = quot;
                    if (!rem.isZero() && !rem.coeff(0).isZero()) {
                        poleTerms.push_back(
                            PoleTerm{lfs[j].root, p, rem.coeff(0)});
                    }
                }
            }

            std::vector<bool> used(poleTerms.size(), false);
            std::vector<Expr> sumPieces;
            bool okZeta = true;
            for (std::size_t i = 0; i < poleTerms.size() && okZeta; ++i) {
                if (used[i])
                    continue;
                std::vector<std::size_t> group{i};
                used[i] = true;
                Rational sumCoeff = poleTerms[i].coeff;
                Rational maxRoot = poleTerms[i].root;
                for (std::size_t j = i + 1; j < poleTerms.size(); ++j) {
                    if (used[j] || poleTerms[j].order != poleTerms[i].order)
                        continue;
                    if ((poleTerms[i].root - poleTerms[j].root).den() ==
                        BigInt(1)) {
                        used[j] = true;
                        group.push_back(j);
                        sumCoeff = sumCoeff + poleTerms[j].coeff;
                        if (maxRoot < poleTerms[j].root)
                            maxRoot = poleTerms[j].root;
                    }
                }
                const int p = poleTerms[i].order;
                if (p == 1 && !sumCoeff.isZero()) {
                    out.status = SymSumResult::Status::Divergent;
                    out.reason = "non-zero logarithmic residue sum (harmonic divergence)";
                    return out;
                }
                if (sumCoeff.isZero()) {
                    // Telescoping coset: sum_{k=a0}^{inf} = -G_coset(a0).
                    const Rational baseVal = Rational(a0) - maxRoot;
                    for (std::size_t idx : group) {
                        const Rational shiftRat = maxRoot - poleTerms[idx].root;
                        std::int64_t s = 0;
                        if (!shiftRat.num().fitsInt64(s) || s < 0 || s > 64) {
                            okZeta = false;
                            break;
                        }
                        Rational partial(std::int64_t{0});
                        for (std::int64_t m = 0; m < s; ++m) {
                            const Rational dVal = baseVal + Rational(m);
                            if (dVal.isZero()) {
                                okZeta = false;
                                break;
                            }
                            partial = partial +
                                      Rational(std::int64_t{1}) /
                                          Rational::powUInt(
                                              dVal,
                                              static_cast<std::uint64_t>(p));
                        }
                        sumPieces.push_back(
                            c.number(-poleTerms[idx].coeff * partial));
                    }
                    continue;
                }
                if (p >= 2 && (p % 2 == 0) && p <= 16) {
                    const Expr zetaP = eulerZetaEven(c, p);
                    for (std::size_t idx : group) {
                        const Rational rt = poleTerms[idx].root;
                        const Rational cf = poleTerms[idx].coeff;
                        if (rt.den() == BigInt(1)) {
                            std::int64_t nStart = 0;
                            if (!(Rational(a0) - rt).num().fitsInt64(nStart) ||
                                nStart < 1 || nStart > 64) {
                                okZeta = false;
                                break;
                            }
                            Rational headSum(std::int64_t{0});
                            for (std::int64_t n = 1; n < nStart; ++n) {
                                headSum = headSum +
                                          Rational(
                                              BigInt(1),
                                              BigInt::powUInt(
                                                  BigInt(n),
                                                  static_cast<std::uint64_t>(p)));
                            }
                            sumPieces.push_back(c.mul(
                                {c.number(cf),
                                 c.add({zetaP, c.number(-headSum)})}));
                        } else if (rt.den() == BigInt(2)) {
                            std::int64_t twoNPlus1 = 0;
                            if (!((Rational(a0) - rt) * Rational(std::int64_t{2}))
                                     .num()
                                     .fitsInt64(twoNPlus1) ||
                                twoNPlus1 < 1 || (twoNPlus1 % 2 == 0) ||
                                twoNPlus1 > 65) {
                                okZeta = false;
                                break;
                            }
                            const std::int64_t nStart = (twoNPlus1 - 1) / 2;
                            const BigInt pow2P =
                                BigInt(1) << static_cast<std::size_t>(p);
                            const Rational oddFactor(pow2P - BigInt(1), pow2P);
                            Rational headSum(std::int64_t{0});
                            for (std::int64_t n = 0; n < nStart; ++n) {
                                headSum = headSum +
                                          Rational(
                                              BigInt(1),
                                              BigInt::powUInt(
                                                  BigInt(2 * n + 1),
                                                  static_cast<std::uint64_t>(p)));
                            }
                            const Expr oddZeta = c.add(
                                {c.mul({c.number(oddFactor), zetaP}),
                                 c.number(-headSum)});
                            sumPieces.push_back(c.mul(
                                {c.number(cf * Rational(pow2P, BigInt(1))),
                                 oddZeta}));
                        } else {
                            okZeta = false;
                            break;
                        }
                    }
                } else {
                    okZeta = false;
                    break;
                }
            }
            if (okZeta) {
                out.value = sumPieces.empty() ? c.zero()
                                              : c.simplify(c.add(sumPieces));
                out.status = SymSumResult::Status::ProvedSymbolic;
                return out;
            }
        }
    }

    // 2c. Alternating rational series sum_{k = a0}^{inf} (-1)^(c1*k + c0) * R(k)
    //     and exponential factorial series sum_{k = a0}^{inf} P(k) * R(k) / factorial(k).
    if (hasIntA) {
        std::vector<Expr> facs;
        if (c.kind(f) == NodeKind::Mul) {
            for (std::size_t i = 0; i < c.childCount(f); ++i)
                facs.push_back(c.child(f, i));
        } else {
            facs.push_back(f);
        }

        // Check for (-1)^(k + s0) alternating factor.
        Expr altExp;
        std::vector<Expr> nonAltFacs;
        for (const Expr &fac : facs) {
            if (altExp.isNull() && c.kind(fac) == NodeKind::Pow &&
                c.child(fac, 0) == c.number(std::int64_t{-1}) &&
                mentionsSymbol(c, c.child(fac, 1), var)) {
                altExp = c.child(fac, 1);
            } else {
                nonAltFacs.push_back(fac);
            }
        }
        std::vector<Expr> altCoeffs;
        if (!altExp.isNull() &&
            extractPolyCoeffsInVar(c, altExp, var, 1, altCoeffs) &&
            altCoeffs.size() == 2) {
            Rational c0Rat, c1Rat;
            std::int64_t c0Int = 0, c1Int = 0;
            if (c.evalExact(altCoeffs[0], {}, c0Rat) &&
                c.evalExact(altCoeffs[1], {}, c1Rat) &&
                c0Rat.den() == BigInt(1) && c1Rat.den() == BigInt(1) &&
                c0Rat.num().fitsInt64(c0Int) && c1Rat.num().fitsInt64(c1Int) &&
                (std::abs(c1Int) % 2 == 1)) {
                const Expr ratPart =
                    nonAltFacs.empty() ? c.one() : c.mul(nonAltFacs);
                UPoly rN, rD;
                if (toRational(c, ratPart, var, rN, rD) && !rD.isZero() &&
                    rN.deg() == 0 && rD.deg() >= 1) {
                    // Check (k + s)^(-p) or (2*k + 1)^(-1)
                    const Rational lcD = rD.lc();
                    UPoly dMon = rD;
                    dMon.makeMonic();
                    const std::vector<UPoly> irs = factorOverQ(dMon, budget);
                    if (!irs.empty()) {
                        bool sameRoot = true;
                        const Rational rt = -irs[0].coeff(0) / irs[0].coeff(1);
                        for (const UPoly &ir : irs) {
                            if (ir.deg() != 1 ||
                                (-ir.coeff(0) / ir.coeff(1)) != rt) {
                                sameRoot = false;
                                break;
                            }
                        }
                        const int p = static_cast<int>(irs.size());
                        const Rational scale =
                            rN.coeff(0) /
                            Rational::powUInt(lcD, static_cast<std::uint64_t>(p));
                        if (sameRoot && rt.den() == BigInt(1)) {
                            std::int64_t rtInt = 0;
                            if (rt.num().fitsInt64(rtInt) && a0 - rtInt >= 1 &&
                                a0 - rtInt <= 32) {
                                const std::int64_t nStart = a0 - rtInt;
                                // For n = k - rtInt >= nStart:
                                // (-1)^(c1*k + c0) = (-1)^(c1*rtInt + c0 + 1) * (-1)^(n - 1).
                                const std::int64_t parity =
                                    (((c1Int * rtInt + c0Int + 1) % 2) + 2) % 2;
                                const std::int64_t sgn =
                                    parity == 0 ? std::int64_t{1}
                                                : std::int64_t{-1};
                                Expr baseSeries;
                                if (p == 1) {
                                    baseSeries =
                                        c.func("log", c.number(std::int64_t{2}));
                                } else if (p >= 2 && (p % 2 == 0) && p <= 16) {
                                    const BigInt pow2 =
                                        BigInt(1)
                                        << static_cast<std::size_t>(p - 1);
                                    const Rational etaFactor(pow2 - BigInt(1),
                                                             pow2);
                                    baseSeries = c.mul(
                                        {c.number(etaFactor),
                                         eulerZetaEven(c, p)});
                                }
                                if (!baseSeries.isNull()) {
                                    Rational head(std::int64_t{0});
                                    for (std::int64_t n = 1; n < nStart; ++n) {
                                        const std::int64_t nSgn =
                                            (n % 2 == 1) ? std::int64_t{1}
                                                         : std::int64_t{-1};
                                        head = head +
                                               Rational(
                                                   BigInt(nSgn),
                                                   BigInt::powUInt(
                                                       BigInt(n),
                                                       static_cast<std::uint64_t>(
                                                           p)));
                                    }
                                    out.value = c.simplify(c.mul(
                                        {c.number(scale * Rational(sgn)),
                                         c.add({baseSeries, c.number(-head)})}));
                                    out.status =
                                        SymSumResult::Status::ProvedSymbolic;
                                    return out;
                                }
                            }
                        } else if (sameRoot && p == 1 && rt.den() == BigInt(2)) {
                            // Gregory-Leibniz: sum (-1)^n / (2*n + 1) = pi/4.
                            std::int64_t twoNPlus1 = 0;
                            if (((Rational(a0) - rt) * Rational(std::int64_t{2}))
                                    .num()
                                    .fitsInt64(twoNPlus1) &&
                                twoNPlus1 >= 1 && (twoNPlus1 % 2 == 1) &&
                                twoNPlus1 <= 65) {
                                const std::int64_t nStart = (twoNPlus1 - 1) / 2;
                                const std::int64_t kShift =
                                    a0 - nStart; // k = n + kShift
                                const std::int64_t parity =
                                    (((c1Int * kShift + c0Int) % 2) + 2) % 2;
                                const std::int64_t sgn =
                                    parity == 0 ? std::int64_t{1}
                                                : std::int64_t{-1};
                                Rational head(std::int64_t{0});
                                for (std::int64_t n = 0; n < nStart; ++n) {
                                    const std::int64_t nSgn =
                                        (n % 2 == 0) ? std::int64_t{1}
                                                     : std::int64_t{-1};
                                    head = head +
                                           Rational(nSgn, BigInt(2 * n + 1));
                                }
                                const Expr piOver4 = c.mul(
                                    {c.number(Rational(std::int64_t{1}, BigInt(4))),
                                     c.symbol("pi")});
                                out.value = c.simplify(c.mul(
                                    {c.number(scale * Rational(std::int64_t{2} * sgn)),
                                     c.add({piOver4, c.number(-head)})}));
                                out.status =
                                    SymSumResult::Status::ProvedSymbolic;
                                return out;
                            }
                        }
                    }
                }
            }
        }

        // Exponential / factorial series: sum_{k = a0}^{inf} P(k) * R(k) / factorial(k)
        // for a0 >= 0.
        if (a0 >= 0 && a0 <= 32) {
            bool hasFactDenom = false;
            std::vector<Expr> remFacs;
            for (const Expr &fac : facs) {
                if (!hasFactDenom && c.kind(fac) == NodeKind::Pow &&
                    c.child(fac, 1) == c.number(std::int64_t{-1}) &&
                    c.kind(c.child(fac, 0)) == NodeKind::Func &&
                    c.funcName(c.child(fac, 0)) == "factorial" &&
                    c.child(c.child(fac, 0), 0) == var) {
                    hasFactDenom = true;
                } else {
                    remFacs.push_back(fac);
                }
            }
            if (hasFactDenom) {
                std::vector<Expr> gFacs, pFacs;
                for (const Expr &rf : remFacs) {
                    if (c.kind(rf) == NodeKind::Pow &&
                        !mentionsSymbol(c, c.child(rf, 0), var) &&
                        mentionsSymbol(c, c.child(rf, 1), var)) {
                        gFacs.push_back(rf);
                    } else if (c.kind(rf) == NodeKind::Func &&
                               c.funcName(rf) == "exp" &&
                               mentionsSymbol(c, c.child(rf, 0), var)) {
                        gFacs.push_back(rf);
                    } else {
                        pFacs.push_back(rf);
                    }
                }
                const Expr R = gFacs.empty() ? c.one() : c.mul(gFacs);
                const Expr r0 = safeSubsAndFold(c, R, var, c.zero());
                const Expr rNext = expandShiftPowers(
                    c, c.subs(R, var, c.add({var, c.one()})), var);
                const Expr q = c.simplify(c.div(rNext, R));
                const Expr pExpr = pFacs.empty() ? c.one() : c.mul(pFacs);
                std::vector<Expr> polyP;
                if (!r0.isNull() && !q.isNull() &&
                    !mentionsSymbol(c, q, var) &&
                    extractPolyCoeffsInVar(c, pExpr, var, 8, polyP)) {
                    // Convert P(k) into falling-factorial basis sum_{j=0}^d beta_j * k^(j)_falling
                    // using forward finite differences at k = 0: beta_j = Delta^j P(0) / j!.
                    const int d = static_cast<int>(polyP.size()) - 1;
                    std::vector<Expr> vals(static_cast<std::size_t>(d + 1));
                    for (int k = 0; k <= d; ++k) {
                        vals[static_cast<std::size_t>(k)] =
                            evalSymbolicPolyInVar(
                                c, polyP,
                                c.number(static_cast<std::int64_t>(k)));
                    }
                    std::vector<Expr> bellTerms;
                    BigInt factJ(1);
                    for (int j = 0; j <= d; ++j) {
                        if (j >= 2)
                            factJ = factJ * BigInt(j);
                        const Expr betaJ = c.simplify(c.mul(
                            {c.number(Rational(BigInt(1), factJ)), vals[0]}));
                        if (!c.isZero(betaJ)) {
                            const Expr qPow =
                                (j == 0)
                                    ? c.one()
                                    : c.pow(q, c.number(
                                                   static_cast<std::int64_t>(j)));
                            bellTerms.push_back(c.mul({betaJ, qPow}));
                        }
                        for (int m = 0; m < d - j; ++m) {
                            vals[static_cast<std::size_t>(m)] = c.simplify(c.add(
                                {vals[static_cast<std::size_t>(m + 1)],
                                 c.neg(vals[static_cast<std::size_t>(m)])}));
                        }
                    }
                    const Expr fullSum = c.mul(
                        {r0, c.func("exp", q),
                         bellTerms.empty() ? c.zero() : c.add(bellTerms)});
                    std::vector<Expr> headTerms{fullSum};
                    for (std::int64_t k = 0; k < a0; ++k) {
                        const Expr fk =
                            safeSubsAndFold(c, f, var, c.number(k));
                        if (!fk.isNull())
                            headTerms.push_back(c.neg(fk));
                    }
                    out.value = c.simplify(c.add(headTerms));
                    out.status = SymSumResult::Status::ProvedSymbolic;
                    return out;
                }
            }
        }

        // Additive linearity over Add for infinite series when every summand
        // converges (or exactly one summand diverges).
        const Expr fExp = c.expand(f);
        if (c.kind(fExp) == NodeKind::Add) {
            std::vector<Expr> pieceVals;
            std::size_t divCount = 0;
            std::size_t unevalCount = 0;
            SymSumResult firstDiv;
            for (std::size_t i = 0; i < c.childCount(fExp); ++i) {
                const SymSumResult si =
                    symsum(c, c.child(fExp, i), var, a, b, budget);
                if (si.proved()) {
                    pieceVals.push_back(si.value);
                } else if (si.status == SymSumResult::Status::Divergent) {
                    ++divCount;
                    if (divCount == 1)
                        firstDiv = si;
                } else {
                    ++unevalCount;
                    break;
                }
            }
            if (divCount == 0 && unevalCount == 0) {
                out.value = c.simplify(c.add(pieceVals));
                out.status = SymSumResult::Status::ProvedSymbolic;
                return out;
            }
            if (divCount == 1 && unevalCount == 0)
                return firstDiv;
        }
    }

    out.reason = "unable to evaluate infinite series in closed form";
    return out;
}

} // namespace numkit::cas
