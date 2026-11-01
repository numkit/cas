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

    // 3. Dilogarithm Taylor series and asymptotic limits
    const Expr tDilog = taylor(c, parseExpr(c, "dilog(x)"), x, c.zero(), 4);
    EXPECT_TRUE(
        exprEq(c, tDilog, parseExpr(c, "x + 1/4*x^2 + 1/9*x^3 + 1/16*x^4")));
    EXPECT_EQ(limitAtInfinity(c, parseExpr(c, "dilog(-x)"), x, +1).status,
              LimitResult::Status::Divergent);
    EXPECT_TRUE(exprEq(
        c,
        limitAtInfinity(c, parseExpr(c, "dilog(-x) + 1/2*log(x)^2"), x, +1)
            .value,
        parseExpr(c, "-1/6*pi^2")));
}

TEST(SeriesTest, SymbolicResiduesAndResidueSumTheorem)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // 1. Simple and higher-order rational and transcendental poles
    EXPECT_EQ(residue(c, parseExpr(c, "1/x"), x, c.zero()), c.one());
    EXPECT_EQ(residue(c, parseExpr(c, "1/x^2"), x, c.zero()), c.zero());
    EXPECT_EQ(residue(c, parseExpr(c, "exp(x)/x^3"), x, c.zero()),
              parseExpr(c, "1/2"));
    EXPECT_EQ(residue(c, parseExpr(c, "sin(x)/x^4"), x, c.zero()),
              parseExpr(c, "-1/6"));
    EXPECT_EQ(residue(c, parseExpr(c, "1/sin(x)"), x, c.zero()), c.one());
    EXPECT_EQ(residue(c, parseExpr(c, "cot(x)"), x, c.zero()), c.one());
    EXPECT_EQ(residue(c, parseExpr(c, "cot(x)/x^2"), x, c.zero()),
              parseExpr(c, "-1/3"));
    EXPECT_EQ(residue(c, parseExpr(c, "1/(x*(x - 1)^2)"), x, c.one()),
              c.number(std::int64_t{-1}));
    EXPECT_EQ(residue(c, parseExpr(c, "(2*x + 3)/((x - 1)*(x + 2))"), x,
                      c.one()),
              parseExpr(c, "5/3"));
    // Analytic point -> residue 0
    EXPECT_EQ(residue(c, parseExpr(c, "sin(x)/x"), x, c.zero()), c.zero());

    // Symbolic pole parameter z0 = a
    EXPECT_TRUE(exprEq(
        c, residue(c, parseExpr(c, "exp(x)/(x - a)^2"), x, c.symbol("a")),
        parseExpr(c, "exp(a)")));

    // 2. Residue at infinity and Cauchy global residue theorem:
    //    For f(x) = (3*x^2 + 2*x + 1)/((x - 1)*(x + 2)*(x - 3)),
    //    Res(f, 1) + Res(f, -2) + Res(f, 3) + Res(f, inf) == 0.
    const Expr fRat = parseExpr(c, "(3*x^2 + 2*x + 1)/((x - 1)*(x + 2)*(x - 3))");
    const Expr r1 = residue(c, fRat, x, c.one());
    const Expr r2 = residue(c, fRat, x, c.number(std::int64_t{-2}));
    const Expr r3 = residue(c, fRat, x, c.number(std::int64_t{3}));
    const Expr rInf = residue(c, fRat, x, c.symbol("inf"));
    ASSERT_FALSE(r1.isNull());
    ASSERT_FALSE(r2.isNull());
    ASSERT_FALSE(r3.isNull());
    ASSERT_FALSE(rInf.isNull());
    EXPECT_EQ(rInf, c.number(std::int64_t{-3}));
    EXPECT_EQ(c.simplify(c.add({r1, r2, r3, rInf})), c.zero());
}

TEST(SeriesTest, SymbolicSummationFiniteAndInfinite)
{
    Ctx c;
    const Expr k = c.symbol("k");
    const Expr n = c.symbol("n");

    struct SumCase
    {
        const char *f;
        const char *a;
        const char *b;
        const char *expected;
    };
    const SumCase cases[] = {
        // 1. Faulhaber-Bernoulli polynomial sums
        {"1", "1", "n", "n"},
        {"k", "1", "n", "1/2*n*(n + 1)"},
        {"k^2", "1", "n", "1/6*n*(n + 1)*(2*n + 1)"},
        {"k^3", "1", "n", "1/4*n^2*(n + 1)^2"},
        {"k^4", "1", "n", "1/30*n*(n + 1)*(2*n + 1)*(3*n^2 + 3*n - 1)"},
        {"3*k^2 + 3*k + 1", "0", "n", "(n + 1)^3"},

        // 2. Geometric and arithmetico-geometric finite and infinite sums
        {"r^k", "0", "n", "(r^(n + 1) - 1)/(r - 1)"},
        {"k*2^k", "1", "n", "(n - 1)*2^(n + 1) + 2"},
        {"(1/2)^k", "0", "inf", "2"},
        {"(-1/2)^k", "0", "inf", "2/3"},
        {"k*(1/2)^k", "0", "inf", "2"},
        {"k^2*(1/2)^k", "0", "inf", "6"},
        {"k*(1/3)^k", "1", "inf", "3/4"},
        {"exp(-2*k)", "0", "inf", "1/(1 - exp(-2))"},

        // 3. Rational and logarithmic telescoping sums (finite & infinite)
        {"1/(k*(k + 1))", "1", "n", "n/(n + 1)"},
        {"1/(k*(k + 1))", "1", "inf", "1"},
        {"1/(k*(k + 2))", "1", "inf", "3/4"},
        {"1/(k*(k + 1)*(k + 2))", "1", "inf", "1/4"},
        {"(2*k + 1)/(k^2*(k + 1)^2)", "1", "n", "1 - 1/(n + 1)^2"},
        {"(2*k + 1)/(k^2*(k + 1)^2)", "1", "inf", "1"},
        {"log((k + 1)/k)", "1", "n", "log(n + 1)"},

        // 4. Classical Euler-Riemann zeta, Dirichlet eta, Gregory-Leibniz, and factorial series
        {"1/k^2", "1", "inf", "1/6*pi^2"},
        {"1/k^2", "2", "inf", "1/6*pi^2 - 1"},
        {"1/k^4", "1", "inf", "1/90*pi^4"},
        {"1/k^6", "1", "inf", "1/945*pi^6"},
        {"1/(2*k + 1)^2", "0", "inf", "1/8*pi^2"},
        {"1/(2*k + 1)^4", "0", "inf", "1/96*pi^4"},
        {"1/(k^2*(k + 1)^2)", "1", "inf", "1/3*pi^2 - 3"},
        {"(-1)^(k - 1)/k", "1", "inf", "log(2)"},
        {"(-1)^k/k", "1", "inf", "-log(2)"},
        {"(-1)^k/(2*k + 1)", "0", "inf", "1/4*pi"},
        {"(-1)^(k - 1)/k^2", "1", "inf", "1/12*pi^2"},
        {"(-1)^(k - 1)/k^4", "1", "inf", "7/720*pi^4"},
        {"1/factorial(k)", "0", "inf", "exp(1)"},
        {"x^k/factorial(k)", "0", "inf", "exp(x)"},
        {"x^k/factorial(k)", "1", "inf", "exp(x) - 1"},
        {"k*x^k/factorial(k)", "0", "inf", "x*exp(x)"},
        {"k^2*x^k/factorial(k)", "0", "inf", "(x^2 + x)*exp(x)"},
    };

    for (const auto &tc : cases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr a = parseExpr(c, tc.a);
        const Expr b = parseExpr(c, tc.b);
        const Expr expVal = parseExpr(c, tc.expected);
        const SymSumResult r = symsum(c, f, k, a, b);
        ASSERT_TRUE(r.proved())
            << "symsum failed for " << tc.f << " on [" << tc.a << ", " << tc.b
            << "]: " << r.reason;
        EXPECT_EQ(c.simplify(c.add({r.value, c.neg(expVal)})), c.zero())
            << "for " << tc.f << " on [" << tc.a << ", " << tc.b
            << "]: got " << c.toString(r.value) << ", expected "
            << c.toString(expVal);

        // When upper bound is symbolic `n`, verify S(5) - S(4) == f(5).
        if (b == n) {
            const Expr s5 = c.subs(r.value, n, c.number(std::int64_t{5}));
            const Expr s4 = c.subs(r.value, n, c.number(std::int64_t{4}));
            const Expr f5 = c.subs(f, k, c.number(std::int64_t{5}));
            EXPECT_EQ(c.simplify(c.add({s5, c.neg(s4), c.neg(f5)})), c.zero())
                << "backward difference S(5) - S(4) != f(5) for " << tc.f;
        }
    }

    // 5. Divergence checks
    EXPECT_EQ(symsum(c, parseExpr(c, "1/k"), k, c.one(), parseExpr(c, "inf")).status,
              SymSumResult::Status::Divergent);
    EXPECT_EQ(symsum(c, parseExpr(c, "1/(2*k + 1)"), k, c.zero(), parseExpr(c, "inf")).status,
              SymSumResult::Status::Divergent);
    EXPECT_EQ(symsum(c, parseExpr(c, "2^k"), k, c.zero(), parseExpr(c, "inf")).status,
              SymSumResult::Status::Divergent);
    EXPECT_EQ(symsum(c, parseExpr(c, "k/(k + 1)"), k, c.one(), parseExpr(c, "inf")).status,
              SymSumResult::Status::Divergent);
}

TEST(SeriesTest, PadeApproximantsAndCertificates)
{
    Ctx c;
    const Expr x = c.symbol("x");

    struct PadeCase
    {
        const char *f;
        const char *x0;
        int m;
        int n;
        const char *expected;
    };
    const PadeCase cases[] = {
        // 1. Classical Pade table of exp(x) at x0 = 0
        {"exp(x)", "0", 1, 1, "(1 + 1/2*x)/(1 - 1/2*x)"},
        {"exp(x)", "0", 2, 1, "(1 + 2/3*x + 1/6*x^2)/(1 - 1/3*x)"},
        {"exp(x)", "0", 1, 2, "(1 + 1/3*x)/(1 - 2/3*x + 1/6*x^2)"},
        {"exp(x)", "0", 2, 2,
         "(1 + 1/2*x + 1/12*x^2)/(1 - 1/2*x + 1/12*x^2)"},
        {"exp(x)", "0", 3, 3,
         "(1 + 1/2*x + 1/10*x^2 + 1/120*x^3)/(1 - 1/2*x + 1/10*x^2 - 1/120*x^3)"},

        // 2. Trigonometric, logarithmic, radical, and special functions
        {"sin(x)", "0", 1, 2, "x/(1 + 1/6*x^2)"},
        {"sin(x)", "0", 3, 2, "(x - 7/60*x^3)/(1 + 1/20*x^2)"},
        {"cos(x)", "0", 2, 2, "(1 - 5/12*x^2)/(1 + 1/12*x^2)"},
        {"cos(x)", "0", 2, 4, "(1 - 61/150*x^2)/(1 + 7/75*x^2 + 1/200*x^4)"},
        {"tan(x)", "0", 3, 2, "(x - 1/15*x^3)/(1 - 2/5*x^2)"},
        {"log(1 + x)", "0", 1, 1, "x/(1 + 1/2*x)"},
        {"log(1 + x)", "0", 2, 2, "(x + 1/2*x^2)/(1 + x + 1/6*x^2)"},
        {"(1 + x)^(1/2)", "0", 1, 1, "(1 + 3/4*x)/(1 + 1/4*x)"},
        {"(1 + x)^(1/2)", "0", 2, 2,
         "(1 + 5/4*x + 5/16*x^2)/(1 + 3/4*x + 1/16*x^2)"},
        {"erf(x)", "0", 3, 2,
         "2*pi^(-1/2)*(x - 1/30*x^3)/(1 + 3/10*x^2)"},
        {"dilog(x)", "0", 2, 1, "(x - 7/36*x^2)/(1 - 4/9*x)"},

        // 3. Non-zero expansion point x0 != 0 and symbolic parameters
        {"log(x)", "1", 1, 1, "(x - 1)/(1 + 1/2*(x - 1))"},
        {"exp(x)", "1", 1, 1, "exp(1)*(1 + 1/2*(x - 1))/(1 - 1/2*(x - 1))"},
        {"exp(a*x)", "0", 1, 1, "(1 + 1/2*a*x)/(1 - 1/2*a*x)"},
        {"1/(1 - a*x)", "0", 2, 2, "1/(1 - a*x)"},
    };

    for (const auto &tc : cases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr x0 = parseExpr(c, tc.x0);
        const Expr expVal = parseExpr(c, tc.expected);
        const PadeResult r = pade(c, f, x, x0, tc.m, tc.n);
        ASSERT_TRUE(r.proved())
            << "pade[" << tc.m << "/" << tc.n << "] failed for " << tc.f
            << " at " << tc.x0 << ": " << r.reason;
        EXPECT_EQ(c.simplify(c.add({r.value, c.neg(expVal)})), c.zero())
            << "for " << tc.f << " [" << tc.m << "/" << tc.n << "]: got "
            << c.toString(r.value) << ", expected " << c.toString(expVal);
        EXPECT_EQ(
            c.simplify(taylor(c, c.add({r.value, c.neg(f)}), x, x0,
                              tc.m + tc.n)),
            c.zero());
    }

    // 4. [m/0] reduces to Taylor polynomial, and degenerate/pole cases return Unevaluated
    const PadeResult padeTaylor =
        pade(c, parseExpr(c, "sin(x)"), x, c.zero(), 5, 0);
    ASSERT_TRUE(padeTaylor.proved());
    EXPECT_TRUE(exprEq(c, padeTaylor.value,
                       taylor(c, parseExpr(c, "sin(x)"), x, c.zero(), 5)));

    EXPECT_FALSE(pade(c, parseExpr(c, "cos(x)"), x, c.zero(), 1, 1).proved());
    EXPECT_FALSE(pade(c, parseExpr(c, "1/x"), x, c.zero(), 1, 1).proved());
}

TEST(SeriesTest, MultivariateTaylorExpansion)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    const Expr z = c.symbol("z");

    // 1. 2D and 3D analytic expansions around the origin
    EXPECT_TRUE(exprEq(
        c, mtaylor(c, parseExpr(c, "exp(x + y)"), {x, y}, {c.zero(), c.zero()}, 2),
        parseExpr(c, "1 + x + y + 1/2*x^2 + x*y + 1/2*y^2")));

    EXPECT_TRUE(exprEq(
        c, mtaylor(c, parseExpr(c, "sin(x)*cos(y)"), {x, y}, {c.zero(), c.zero()}, 3),
        parseExpr(c, "x - 1/6*x^3 - 1/2*x*y^2")));

    EXPECT_TRUE(exprEq(
        c, mtaylor(c, parseExpr(c, "1/(1 - x - y)"), {x, y}, {c.zero(), c.zero()}, 2),
        parseExpr(c, "1 + x + y + x^2 + 2*x*y + y^2")));

    EXPECT_TRUE(exprEq(
        c, mtaylor(c, parseExpr(c, "log(1 + x + y)"), {x, y}, {c.zero(), c.zero()}, 2),
        parseExpr(c, "x + y - 1/2*x^2 - x*y - 1/2*y^2")));

    EXPECT_TRUE(exprEq(
        c,
        mtaylor(c, parseExpr(c, "(1 + x + y^2)^(1/2)"), {x, y},
                {c.zero(), c.zero()}, 2),
        parseExpr(c, "1 + 1/2*x - 1/8*x^2 + 1/2*y^2")));

    EXPECT_TRUE(exprEq(
        c,
        mtaylor(c, parseExpr(c, "exp(x)*sin(y + z)"), {x, y, z},
                {c.zero(), c.zero(), c.zero()}, 2),
        parseExpr(c, "y + z + x*y + x*z")));

    // 2. Non-zero expansion point (x0, y0) = (1, 2)
    const Expr mtShift = mtaylor(c, parseExpr(c, "x^2*y + y^2"), {x, y},
                                 {c.one(), c.number(std::int64_t{2})}, 2);
    ASSERT_FALSE(mtShift.isNull());
    EXPECT_TRUE(exprEq(
        c, mtShift,
        parseExpr(
            c,
            "6 + 4*(x - 1) + 5*(y - 2) + 2*(x - 1)^2 + 2*(x - 1)*(y - 2) + (y - 2)^2")));

    // 3. Removable homogeneous singularity cancellation
    const Expr mtRem = mtaylor(
        c, parseExpr(c, "(sin(x + y) - (x + y))/(x + y)^3"), {x, y},
        {c.zero(), c.zero()}, 2);
    ASSERT_FALSE(mtRem.isNull());
    EXPECT_TRUE(exprEq(
        c, mtRem, parseExpr(c, "-1/6 + 1/120*x^2 + 1/60*x*y + 1/120*y^2")));

    // 4. Non-analytic / pole rejection at (0, 0)
    EXPECT_TRUE(
        mtaylor(c, parseExpr(c, "1/(x + y)"), {x, y}, {c.zero(), c.zero()}, 2)
            .isNull());
    EXPECT_TRUE(
        mtaylor(c, parseExpr(c, "x*y/(x^2 + y^2)"), {x, y},
                {c.zero(), c.zero()}, 2)
            .isNull());
    EXPECT_TRUE(
        mtaylor(c, parseExpr(c, "x^2/(x + y)"), {x, y}, {c.zero(), c.zero()}, 0)
            .isNull());
}

TEST(SeriesTest, PropertyPadeAndMultivariateTaylor)
{
    std::mt19937_64 rng(0x5A17E55EEDULL);
    std::uniform_int_distribution<std::int64_t> coefDist(-4, 4);

    // 1. Pade [2/2] exactly recovers any rational function P(x)/Q(x) with
    //    deg(P) <= 2, deg(Q) <= 2, Q(0) = 1.
    for (int iter = 0; iter < 50; ++iter) {
        Ctx c;
        const Expr x = c.symbol("x");
        const Expr p0 = c.number(coefDist(rng));
        const Expr p1 = c.number(coefDist(rng));
        const Expr p2 = c.number(coefDist(rng));
        const Expr q1 = c.number(coefDist(rng));
        const Expr q2 = c.number(coefDist(rng));
        const Expr P = c.add(
            {p0, c.mul({p1, x}), c.mul({p2, c.pow(x, c.number(std::int64_t{2}))})});
        const Expr Q = c.add(
            {c.one(), c.mul({q1, x}),
             c.mul({q2, c.pow(x, c.number(std::int64_t{2}))})});
        const Expr rat = c.div(P, Q);
        const PadeResult r = pade(c, rat, x, c.zero(), 2, 2);
        ASSERT_TRUE(r.proved()) << "iter " << iter << ": " << r.reason;
        EXPECT_EQ(c.simplify(c.add({r.value, c.neg(rat)})), c.zero());
    }

    // 2. Multivariate Taylor commutes with partial differentiation:
    //    d/dx mtaylor(f, 3) == mtaylor(df/dx, 2) and
    //    d/dy mtaylor(f, 3) == mtaylor(df/dy, 2).
    {
        Ctx c;
        const Expr x = c.symbol("x");
        const Expr y = c.symbol("y");
        const Expr f = parseExpr(c, "exp(x + 2*y)*cos(x - y)");
        const Expr mt3 = mtaylor(c, f, {x, y}, {c.zero(), c.zero()}, 3);
        ASSERT_FALSE(mt3.isNull());
        const Expr dMtDx = c.expand(c.diff(mt3, x));
        const Expr dMtDy = c.expand(c.diff(mt3, y));
        const Expr mtDfDx =
            c.expand(mtaylor(c, c.diff(f, x), {x, y}, {c.zero(), c.zero()}, 2));
        const Expr mtDfDy =
            c.expand(mtaylor(c, c.diff(f, y), {x, y}, {c.zero(), c.zero()}, 2));
        EXPECT_EQ(dMtDx, mtDfDx);
        EXPECT_EQ(dMtDy, mtDfDy);
    }
}

TEST(SeriesTest, GammaDigammaLaurentResidueAndPolygammaSymsum)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr k = c.symbol("k");
    const Expr n = c.symbol("n");

    // 1. Taylor/Laurent expansions and residues of gamma, lgamma, digamma
    const Expr tLg = taylor(c, parseExpr(c, "lgamma(1 + x)"), x, c.zero(), 2);
    ASSERT_FALSE(tLg.isNull());
    EXPECT_TRUE(exprEq(c, tLg, parseExpr(c, "-euler_gamma*x + pi^2/12*x^2")));

    const Expr tGam = taylor(c, parseExpr(c, "gamma(1 + x)"), x, c.zero(), 2);
    ASSERT_FALSE(tGam.isNull());
    EXPECT_TRUE(exprEq(
        c, tGam,
        parseExpr(c, "1 - euler_gamma*x + (1/2*euler_gamma^2 + pi^2/12)*x^2")));

    const Expr lGam0 = laurent(c, parseExpr(c, "gamma(x)"), x, c.zero(), 1);
    ASSERT_FALSE(lGam0.isNull());
    EXPECT_TRUE(exprEq(
        c, lGam0,
        parseExpr(c, "1/x - euler_gamma + (1/2*euler_gamma^2 + pi^2/12)*x")));

    const Expr lPsi0 = laurent(c, parseExpr(c, "digamma(x)"), x, c.zero(), 1);
    ASSERT_FALSE(lPsi0.isNull());
    EXPECT_TRUE(
        exprEq(c, lPsi0, parseExpr(c, "-1/x - euler_gamma + pi^2/6*x")));

    EXPECT_EQ(residue(c, parseExpr(c, "gamma(x)"), x, c.zero()), c.one());
    EXPECT_EQ(residue(c, parseExpr(c, "gamma(x)"), x, c.number(-1)),
              c.number(-1));
    EXPECT_EQ(residue(c, parseExpr(c, "gamma(x)"), x, c.number(-2)),
              c.number(Rational(1, BigInt(2))));
    EXPECT_EQ(residue(c, parseExpr(c, "gamma(x)"), x, c.number(-3)),
              c.number(Rational(-1, BigInt(6))));
    EXPECT_EQ(residue(c, parseExpr(c, "digamma(x)"), x, c.number(-2)),
              c.number(-1));

    const LimitResult limGam =
        limit(c, parseExpr(c, "(gamma(1 + x) - 1)/x"), x, c.zero());
    ASSERT_TRUE(limGam.proved());
    EXPECT_EQ(limGam.value, parseExpr(c, "-euler_gamma"));

    // 2. Closed-form finite rational sums via digamma and trigamma
    const SymSumResult sHarm =
        symsum(c, parseExpr(c, "1/k"), k, c.one(), n);
    ASSERT_TRUE(sHarm.proved()) << sHarm.reason;
    EXPECT_TRUE(
        exprEq(c, sHarm.value, parseExpr(c, "digamma(n + 1) + euler_gamma")));

    const SymSumResult sSq =
        symsum(c, parseExpr(c, "1/k^2"), k, c.one(), n);
    ASSERT_TRUE(sSq.proved()) << sSq.reason;
    EXPECT_TRUE(
        exprEq(c, sSq.value, parseExpr(c, "pi^2/6 - trigamma(n + 1)")));

    const SymSumResult sOdd =
        symsum(c, parseExpr(c, "1/(2*k - 1)"), k, c.one(), n);
    ASSERT_TRUE(sOdd.proved()) << sOdd.reason;
    EXPECT_TRUE(exprEq(
        c, sOdd.value,
        parseExpr(c, "1/2*digamma(n + 1/2) + 1/2*euler_gamma + log(2)")));

    // 3. Maclaurin series of Bessel J_0, J_1, I_0 and Airy Ai
    const Expr tJ0 = taylor(c, parseExpr(c, "besselj(0, x)"), x, c.zero(), 4);
    ASSERT_FALSE(tJ0.isNull());
    EXPECT_TRUE(exprEq(c, tJ0, parseExpr(c, "1 - 1/4*x^2 + 1/64*x^4")));

    const Expr tJ1 = taylor(c, parseExpr(c, "besselj(1, x)"), x, c.zero(), 5);
    ASSERT_FALSE(tJ1.isNull());
    EXPECT_TRUE(
        exprEq(c, tJ1, parseExpr(c, "1/2*x - 1/16*x^3 + 1/384*x^5")));

    const Expr tI0 = taylor(c, parseExpr(c, "besseli(0, x)"), x, c.zero(), 4);
    ASSERT_FALSE(tI0.isNull());
    EXPECT_TRUE(exprEq(c, tI0, parseExpr(c, "1 + 1/4*x^2 + 1/64*x^4")));
}

} // namespace
} // namespace numkit::cas
