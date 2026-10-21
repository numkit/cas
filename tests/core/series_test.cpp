#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/core/series.hpp>

#include <gtest/gtest.h>

#include <cmath>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

namespace numkit::cas {
namespace {

bool exprEq(Ctx &c, Expr a, Expr b)
{
    if (a.isNull() || b.isNull())
        return a.isNull() && b.isNull();
    return c.expand(c.add({a, c.neg(b)})) == c.zero();
}

// ============================================================================
// Layer 1: Fixed Oracle Vectors
// ============================================================================

TEST(SeriesTest, TaylorElementaryMaclaurin)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr x0 = c.zero();

    struct Case {
        const char *f;
        int order;
        const char *expected;
    };
    const Case cases[] = {
        {"sin(x)", 5, "x - 1/6*x^3 + 1/120*x^5"},
        {"cos(x)", 5, "1 - 1/2*x^2 + 1/24*x^4"},
        {"tan(x)", 5, "x + 1/3*x^3 + 2/15*x^5"},
        {"exp(x)", 4, "1 + x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4"},
        {"log(1 + x)", 4, "x - 1/2*x^2 + 1/3*x^3 - 1/4*x^4"},
        {"1/(1 - x)", 4, "1 + x + x^2 + x^3 + x^4"},
        {"sqrt(1 + x)", 3, "1 + 1/2*x - 1/8*x^2 + 1/16*x^3"},
        {"(1 + x)^(-1/2)", 3, "1 - 1/2*x + 3/8*x^2 - 5/16*x^3"},
        {"asin(x)", 5, "x + 1/6*x^3 + 3/40*x^5"},
        {"atan(x)", 5, "x - 1/3*x^3 + 1/5*x^5"},
        {"sinh(x)", 5, "x + 1/6*x^3 + 1/120*x^5"},
        {"cosh(x)", 5, "1 + 1/2*x^2 + 1/24*x^4"},
        {"tanh(x)", 5, "x - 1/3*x^3 + 2/15*x^5"},
        {"asinh(x)", 5, "x - 1/6*x^3 + 3/40*x^5"},
        {"atanh(x)", 5, "x + 1/3*x^3 + 1/5*x^5"},
    };

    for (const auto &tc : cases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr want = parseExpr(c, tc.expected);
        const Expr got = taylor(c, f, x, x0, tc.order);
        ASSERT_FALSE(got.isNull()) << "failed on " << tc.f;
        EXPECT_TRUE(exprEq(c, got, want))
            << "f = " << tc.f << "\n  got:  " << c.toString(got)
            << "\n  want: " << c.toString(want);
    }
}

TEST(SeriesTest, TaylorCompositeAndRemovableSingularities)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr x0 = c.zero();

    struct Case {
        const char *f;
        int order;
        const char *expected;
    };
    const Case cases[] = {
        {"exp(sin(x))", 4, "1 + x + 1/2*x^2 - 1/8*x^4"},
        {"log(cos(x))", 5, "-1/2*x^2 - 1/12*x^4"},
        {"sin(x)/x", 4, "1 - 1/6*x^2 + 1/120*x^4"},
        {"(1 - cos(x))/x^2", 4, "1/2 - 1/24*x^2 + 1/720*x^4"},
        {"(exp(x) - 1 - x)/x^2", 3, "1/2 + 1/6*x + 1/24*x^2 + 1/120*x^3"},
        {"(tan(x) - sin(x))/x^3", 3, "1/2 + 1/8*x^2"},
    };

    for (const auto &tc : cases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr want = parseExpr(c, tc.expected);
        const Expr got = taylor(c, f, x, x0, tc.order);
        ASSERT_FALSE(got.isNull()) << "failed on " << tc.f;
        EXPECT_TRUE(exprEq(c, got, want))
            << "f = " << tc.f << "\n  got:  " << c.toString(got)
            << "\n  want: " << c.toString(want);
    }
}

TEST(SeriesTest, TaylorNonZeroAndSymbolicPoints)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr a = c.symbol("a");

    // log(x) around x0 = 1
    {
        const Expr f = parseExpr(c, "log(x)");
        const Expr got = taylor(c, f, x, c.one(), 3);
        const Expr want =
            parseExpr(c, "(x - 1) - 1/2*(x - 1)^2 + 1/3*(x - 1)^3");
        ASSERT_FALSE(got.isNull());
        EXPECT_TRUE(exprEq(c, got, want)) << "got: " << c.toString(got);
    }

    // 1/x around x0 = 2
    {
        const Expr f = parseExpr(c, "1/x");
        const Expr got = taylor(c, f, x, c.number(std::int64_t{2}), 3);
        const Expr want =
            parseExpr(c, "1/2 - 1/4*(x - 2) + 1/8*(x - 2)^2 - 1/16*(x - 2)^3");
        ASSERT_FALSE(got.isNull());
        EXPECT_TRUE(exprEq(c, got, want)) << "got: " << c.toString(got);
    }

    // x^3 around symbolic x0 = a
    {
        const Expr f = parseExpr(c, "x^3");
        const Expr got = taylor(c, f, x, a, 3);
        const Expr want =
            parseExpr(c, "a^3 + 3*a^2*(x - a) + 3*a*(x - a)^2 + (x - a)^3");
        ASSERT_FALSE(got.isNull());
        EXPECT_TRUE(exprEq(c, got, want)) << "got: " << c.toString(got);
    }
}

TEST(SeriesTest, LaurentPolesAndMeromorphicCancellation)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr x0 = c.zero();

    // cot(x) = cos(x)/sin(x) = 1/x - 1/3*x - 1/45*x^3 + O(x^4)
    {
        const Expr f = parseExpr(c, "cos(x)/sin(x)");
        const Expr got = laurent(c, f, x, x0, 3);
        const Expr want = parseExpr(c, "1/x - 1/3*x - 1/45*x^3");
        ASSERT_FALSE(got.isNull());
        EXPECT_TRUE(exprEq(c, c.mul({got, x}), c.mul({want, x})))
            << "got: " << c.toString(got);
    }

    // (exp(x) - 1)/x^3 = 1/x^2 + 1/(2*x) + 1/6 + 1/24*x + O(x^2)
    {
        const Expr f = parseExpr(c, "(exp(x) - 1)/x^3");
        const Expr got = laurent(c, f, x, x0, 1);
        const Expr want = parseExpr(c, "1/x^2 + 1/2*1/x + 1/6 + 1/24*x");
        ASSERT_FALSE(got.isNull());
        const Expr x2 = c.pow(x, c.number(std::int64_t{2}));
        EXPECT_TRUE(exprEq(c, c.mul({got, x2}), c.mul({want, x2})))
            << "got: " << c.toString(got);
    }
}

TEST(SeriesTest, LimitFixedVectors)
{
    Ctx c;
    const Expr x = c.symbol("x");

    struct Case {
        const char *f;
        const char *x0;
        const char *expected;
    };
    const Case cases[] = {
        {"sin(x)/x", "0", "1"},
        {"(1 - cos(x))/x^2", "0", "1/2"},
        {"(tan(x) - sin(x))/x^3", "0", "1/2"},
        {"(exp(x) - 1 - x - 1/2*x^2)/x^3", "0", "1/6"},
        {"(log(1 + x) - x)/x^2", "0", "-1/2"},
        {"(sqrt(1 + x) - 1)/x", "0", "1/2"},
        {"(x^3 - 1)/(x - 1)", "1", "3"},
        {"(x^3 - a^3)/(x - a)", "a", "3*a^2"},
        {"1/sin(x) - 1/x", "0", "0"},
        {"1/x^2 - 1/sin(x)^2", "0", "-1/3"},
        {"(asin(x) - x)/x^3", "0", "1/6"},
        {"(atan(x) - x)/x^3", "0", "-1/3"},
        {"x*log(x)", "0", "0"},
        {"x^2*log(x)", "0", "0"},
    };

    for (const auto &tc : cases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr x0 = parseExpr(c, tc.x0);
        const Expr want = parseExpr(c, tc.expected);
        const LimitResult r = limit(c, f, x, x0);
        ASSERT_EQ(r.status, LimitResult::Status::Proved)
            << "failed on " << tc.f << " (" << r.reason << ")";
        EXPECT_TRUE(exprEq(c, r.value, want))
            << "f = " << tc.f << " at x0 = " << tc.x0
            << "\n  got:  " << c.toString(r.value)
            << "\n  want: " << c.toString(want);
    }
}

TEST(SeriesTest, LimitDetectsPoles)
{
    Ctx c;
    const Expr x = c.symbol("x");

    {
        const LimitResult r = limit(c, parseExpr(c, "1/x^3"), x, c.zero());
        EXPECT_EQ(r.status, LimitResult::Status::Divergent);
        EXPECT_EQ(r.poleOrder, 3);
    }
    {
        const LimitResult r = limit(c, parseExpr(c, "1/sin(x)^2"), x, c.zero());
        EXPECT_EQ(r.status, LimitResult::Status::Divergent);
        EXPECT_EQ(r.poleOrder, 2);
    }
}

TEST(SeriesTest, LimitAtInfinityAndOneSidedVectors)
{
    Ctx c;
    const Expr x = c.symbol("x");

    struct InfCase {
        const char *f;
        const char *x0;
        const char *expected;
    };
    const InfCase infCases[] = {
        {"(3*x^2 + 5*x - 1)/(2*x^2 - 7)", "inf", "3/2"},
        {"(3*x^2 + 5*x - 1)/(2*x^2 - 7)", "-inf", "3/2"},
        {"(x + 1)/(x^2 + 1)", "oo", "0"},
        {"atan(x)", "inf", "1/2*pi"},
        {"atan(x)", "-inf", "-1/2*pi"},
        {"x*(pi/2 - atan(x))", "inf", "1"},
        {"exp(-x)", "inf", "0"},
        {"x^3*exp(-2*x)", "inf", "0"},
        {"exp(2*x)", "-inf", "0"},
        {"tanh(x)", "inf", "1"},
        {"tanh(x)", "-inf", "-1"},
        {"log(x + 1) - log(x + 2)", "inf", "0"},
        {"log(3*x + 1) - log(x + 2)", "inf", "log(3)"},
        {"sin(x)/x", "inf", "0"},
        {"cos(2*x)*exp(-x)", "inf", "0"},
        {"sqrt(x^2 + 2*x) - x", "inf", "1"},
    };

    for (const auto &tc : infCases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr x0 = parseExpr(c, tc.x0);
        const Expr want = parseExpr(c, tc.expected);
        const LimitResult r = limit(c, f, x, x0);
        ASSERT_EQ(r.status, LimitResult::Status::Proved)
            << "failed on " << tc.f << " at " << tc.x0 << " (" << r.reason << ")";
        EXPECT_TRUE(exprEq(c, c.simplify(r.value), c.simplify(want)))
            << "f = " << tc.f << " at x0 = " << tc.x0
            << "\n  got:  " << c.toString(r.value)
            << "\n  want: " << c.toString(want);
    }

    // One-sided limits at branch points and finite points
    {
        const LimitResult r = limitOneSided(c, parseExpr(c, "sqrt(x)"), x, c.zero(), +1);
        ASSERT_EQ(r.status, LimitResult::Status::Proved) << r.reason;
        EXPECT_EQ(r.value, c.zero());
    }
    {
        const LimitResult r =
            limitOneSided(c, parseExpr(c, "sqrt(1 - x)"), x, c.one(), -1);
        ASSERT_EQ(r.status, LimitResult::Status::Proved) << r.reason;
        EXPECT_EQ(r.value, c.zero());
    }
    {
        const LimitResult r =
            limitOneSided(c, parseExpr(c, "x*log(x)"), x, c.zero(), +1);
        ASSERT_EQ(r.status, LimitResult::Status::Proved) << r.reason;
        EXPECT_EQ(r.value, c.zero());
    }
    // Divergent polynomial at +inf
    {
        const LimitResult r = limitAtInfinity(c, parseExpr(c, "x^2 + 1"), x, +1);
        EXPECT_EQ(r.status, LimitResult::Status::Divergent);
    }
}

// ============================================================================
// Layer 2: Property Tests
// ============================================================================

TEST(SeriesTest, PropertyPolynomialExactRecovery)
{
    Ctx c;
    const Expr x = c.symbol("x");
    std::mt19937 rng(0x5E21E501u);
    std::uniform_int_distribution<int> coeffDist(-20, 20);
    std::uniform_int_distribution<int> ptDist(-5, 5);

    for (int iter = 0; iter < 200; ++iter) {
        std::vector<Expr> terms;
        for (int d = 0; d <= 5; ++d) {
            const int k = coeffDist(rng);
            if (k != 0) {
                terms.push_back(c.mul({c.number(static_cast<std::int64_t>(k)),
                                       c.pow(x, c.number(static_cast<std::int64_t>(d)))}));
            }
        }
        const Expr poly = terms.empty() ? c.zero() : c.add(terms);
        const Expr x0 = c.number(static_cast<std::int64_t>(ptDist(rng)));
        const Expr t = taylor(c, poly, x, x0, 5);
        ASSERT_FALSE(t.isNull());
        EXPECT_TRUE(exprEq(c, t, poly))
            << "iter " << iter << ": poly=" << c.toString(poly)
            << ", x0=" << c.toString(x0) << ", taylor=" << c.toString(t);
    }
}

TEST(SeriesTest, PropertyDerivativeCommutesWithTaylor)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr x0 = c.zero();

    const char *funcs[] = {
        "sin(x)*exp(x)",
        "cos(x)/(1 + x)",
        "log(1 + x)*sin(x)",
        "sqrt(1 + x)*exp(-x)",
        "atan(x) + sinh(x)",
    };

    for (const char *src : funcs) {
        const Expr f = parseExpr(c, src);
        const Expr df = c.diff(f, x);
        // d/dx(T_5(f)) == T_4(f')
        const Expr t5 = taylor(c, f, x, x0, 5);
        const Expr t4_df = taylor(c, df, x, x0, 4);
        ASSERT_FALSE(t5.isNull());
        ASSERT_FALSE(t4_df.isNull());
        const Expr dt5 = c.diff(t5, x);
        EXPECT_TRUE(exprEq(c, dt5, t4_df))
            << "f = " << src << "\n  d(T5)/dx: " << c.toString(dt5)
            << "\n  T4(df):   " << c.toString(t4_df);
    }
}

TEST(SeriesTest, PropertyNumericalApproximation)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr x0 = c.zero();

    const char *funcs[] = {
        "sin(x) + cos(2*x)",
        "exp(x)/(1 + x^2)",
        "log(1 + x)*sqrt(1 + x)",
        "atan(x)*cosh(x)",
    };

    const double h = 0.05; // |h|^6 ~ 1.5e-8
    for (const char *src : funcs) {
        const Expr f = parseExpr(c, src);
        const Expr t5 = taylor(c, f, x, x0, 5);
        ASSERT_FALSE(t5.isNull());
        double exactVal = 0.0, approxVal = 0.0;
        ASSERT_TRUE(c.evalDouble(f, {{"x", h}}, exactVal));
        ASSERT_TRUE(c.evalDouble(t5, {{"x", h}}, approxVal));
        EXPECT_NEAR(exactVal, approxVal, 1e-6) << "f = " << src;
    }
}

// ============================================================================
// Layer 3: Boundary Tests
// ============================================================================

TEST(SeriesTest, BoundaryCases)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // order = 0 returns f(x0); negative order returns null Expr
    EXPECT_EQ(taylor(c, parseExpr(c, "exp(x)"), x, c.zero(), 0), c.one());
    EXPECT_TRUE(taylor(c, parseExpr(c, "exp(x)"), x, c.zero(), -1).isNull());

    // Pole at x0: taylor returns null, laurent succeeds
    const Expr invX = parseExpr(c, "1/x");
    EXPECT_TRUE(taylor(c, invX, x, c.zero(), 4).isNull());
    EXPECT_FALSE(laurent(c, invX, x, c.zero(), 4).isNull());

    // Branch point at x0 = 0: log(x) and sqrt(x) return null cleanly
    EXPECT_TRUE(taylor(c, parseExpr(c, "log(x)"), x, c.zero(), 4).isNull());
    EXPECT_TRUE(laurent(c, parseExpr(c, "sqrt(x)"), x, c.zero(), 4).isNull());

    // Expression independent of x
    const Expr constExpr = parseExpr(c, "a^2 + 3");
    EXPECT_TRUE(exprEq(c, taylor(c, constExpr, x, c.zero(), 5), constExpr));
    const LimitResult lr = limit(c, constExpr, x, c.zero());
    EXPECT_EQ(lr.status, LimitResult::Status::Proved);
    EXPECT_TRUE(exprEq(c, lr.value, constExpr));
}

TEST(SeriesTest, SpecialFunctionsTaylorAndLimits)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // 1. Taylor series of erf, erfi, Si, FresnelS, FresnelC around x0 = 0
    EXPECT_TRUE(exprEq(
        c, taylor(c, parseExpr(c, "erf(x)"), x, c.zero(), 5),
        parseExpr(c, "(2*x - 2/3*x^3 + 1/5*x^5)*pi^(-1/2)")));
    EXPECT_TRUE(exprEq(
        c, taylor(c, parseExpr(c, "erfc(x)"), x, c.zero(), 5),
        parseExpr(c, "1 - (2*x - 2/3*x^3 + 1/5*x^5)*pi^(-1/2)")));
    EXPECT_TRUE(exprEq(
        c, taylor(c, parseExpr(c, "erfi(x)"), x, c.zero(), 5),
        parseExpr(c, "(2*x + 2/3*x^3 + 1/5*x^5)*pi^(-1/2)")));
    EXPECT_TRUE(exprEq(
        c, taylor(c, parseExpr(c, "Si(x)"), x, c.zero(), 5),
        parseExpr(c, "x - 1/18*x^3 + 1/600*x^5")));
    EXPECT_TRUE(exprEq(
        c, taylor(c, parseExpr(c, "FresnelC(x)"), x, c.zero(), 5),
        parseExpr(c, "x - 1/40*pi^2*x^5")));
    EXPECT_TRUE(exprEq(
        c, taylor(c, parseExpr(c, "FresnelS(x)"), x, c.zero(), 7),
        parseExpr(c, "1/6*pi*x^3 - 1/336*pi^3*x^7")));

    // 2. Taylor series of Ei, Ci around x0 = 1 and li around x0 = 2
    const Expr tEi = taylor(c, parseExpr(c, "Ei(x)"), x, c.one(), 2);
    ASSERT_FALSE(tEi.isNull());
    EXPECT_TRUE(exprEq(c, tEi, parseExpr(c, "Ei(1) + exp(1)*(x - 1)")));

    const Expr tCi = taylor(c, parseExpr(c, "Ci(x)"), x, c.one(), 2);
    ASSERT_FALSE(tCi.isNull());
    EXPECT_TRUE(exprEq(
        c, tCi,
        parseExpr(c, "Ci(1) + cos(1)*(x - 1) - 1/2*(cos(1) + sin(1))*(x - 1)^2")));

    const Expr tLi = taylor(c, parseExpr(c, "li(x)"), x, c.number(std::int64_t{2}), 1);
    ASSERT_FALSE(tLi.isNull());
    EXPECT_TRUE(exprEq(c, tLi, parseExpr(c, "li(2) + (x - 2)/log(2)")));

    // 3. Asymptotic limits at +/- infinity
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "erf(x)"), x, +1).value, c.one());
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "erf(x)"), x, -1).value,
              c.number(std::int64_t{-1}));
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "erfc(x)"), x, +1).value, c.zero());
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "erfc(x)"), x, -1).value,
              c.number(std::int64_t{2}));
    EXPECT_TRUE(exprEq(c, limitAtInfinity(c, parseExpr(c, "Si(x)"), x, +1).value,
                       parseExpr(c, "1/2*pi")));
    EXPECT_TRUE(exprEq(c, limitAtInfinity(c, parseExpr(c, "Si(x)"), x, -1).value,
                       parseExpr(c, "-1/2*pi")));
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "Ci(x)"), x, +1).value, c.zero());
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "Ei(x)"), x, -1).value, c.zero());
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "Ei(x)"), x, +1).status,
              LimitResult::Status::Divergent);
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "erfi(x)"), x, +1).status,
              LimitResult::Status::Divergent);
    EXPECT_TRUE(exprEq(
        c, limitAtInfinity(c, parseExpr(c, "FresnelS(x)"), x, +1).value,
        parseExpr(c, "1/2")));
    EXPECT_TRUE(exprEq(
        c, limitAtInfinity(c, parseExpr(c, "FresnelC(x)"), x, -1).value,
        parseExpr(c, "-1/2")));
}

} // namespace
} // namespace numkit::cas
