#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/core/simplify.hpp>

#include <gtest/gtest.h>

#include <cmath>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

namespace numkit::cas {
namespace {

// ============================================================================
// Layer 1: Fixed Oracle Vectors
// ============================================================================

TEST(SimplifyTest, PythagoreanAndHyperbolicIdentities)
{
    Ctx c;
    struct Case {
        const char *in;
        const char *expected;
    };
    const Case cases[] = {
        {"sin(x)^2 + cos(x)^2", "1"},
        {"r*cos(th)^2 + r*sin(th)^2", "r"},
        {"1 - sin(x)^2", "cos(x)^2"},
        {"1 - cos(x)^2", "sin(x)^2"},
        {"cosh(x)^2 - sinh(x)^2", "1"},
        {"1 + sinh(x)^2", "cosh(x)^2"},
        {"cosh(x)^2 - 1", "sinh(x)^2"},
        {"(sin(x) + cos(x))^2 - 2*sin(x)*cos(x)", "1"},
        {"cos(x)^2 - sin(x)^2", "cos(2*x)"},
        {"cosh(x)^2 + sinh(x)^2", "cosh(2*x)"},
        {"2*sin(x)*cos(x)", "sin(2*x)"},
        {"1/2 - 1/2*cos(2*x) - sin(x)^2", "0"},
        {"sin(2*x)/(2*cos(x))", "sin(x)"},
    };

    for (const auto &tc : cases) {
        const Expr e = parseExpr(c, tc.in);
        const Expr want = parseExpr(c, tc.expected);
        const Expr got = c.simplify(e);
        EXPECT_EQ(got, want)
            << "in:   " << tc.in << "\n  got:  " << c.toString(got)
            << "\n  want: " << c.toString(want);
    }
}

TEST(SimplifyTest, CrossTrigAndParityIdentities)
{
    Ctx c;
    struct Case {
        const char *in;
        const char *expected;
    };
    const Case cases[] = {
        {"sin(x)/cos(x)", "tan(x)"},
        {"sinh(x)/cosh(x)", "tanh(x)"},
        {"cos(x)*tan(x)", "sin(x)"},
        {"sin(x)/tan(x)", "cos(x)"},
        {"(1 - cos(x)^2)/sin(x)", "sin(x)"},
        {"(1 + tan(x)^2)*cos(x)^2", "1"},
        {"sin(-x) + sin(x)", "0"},
        {"cos(-x) - cos(x)", "0"},
        {"tan(-x) + tan(x)", "0"},
        {"sinh(-x) + sinh(x)", "0"},
        {"cosh(-x) - cosh(x)", "0"},
    };

    for (const auto &tc : cases) {
        const Expr e = parseExpr(c, tc.in);
        const Expr want = parseExpr(c, tc.expected);
        const Expr got = c.simplify(e);
        EXPECT_EQ(got, want)
            << "in:   " << tc.in << "\n  got:  " << c.toString(got)
            << "\n  want: " << c.toString(want);
    }
}

TEST(SimplifyTest, InverseFunctionAndExpLogIdentities)
{
    Ctx c;
    struct Case {
        const char *in;
        const char *expected;
    };
    const Case cases[] = {
        {"exp(log(x))", "x"},
        {"log(exp(x))", "x"},
        {"exp(2*log(x))", "x^2"},
        {"exp(x)*exp(-x)", "1"},
        {"exp(x)*exp(y)", "exp(x + y)"},
        {"log(x + 1) + log(x - 1) - log(x^2 - 1)", "0"},
        {"sin(asin(x))", "x"},
        {"cos(acos(x))", "x"},
        {"tan(atan(x))", "x"},
        {"sinh(asinh(x))", "x"},
        {"cosh(acosh(x))", "x"},
        {"tanh(atanh(x))", "x"},
        {"cos(asin(x))", "(1 - x^2)^(1/2)"},
        {"sin(acos(x))", "(1 - x^2)^(1/2)"},
        {"cos(atan(x))", "(1 + x^2)^(-1/2)"},
        {"sin(atan(x))", "x*(1 + x^2)^(-1/2)"},
        {"sqrt(x)^2", "x"},
    };

    for (const auto &tc : cases) {
        const Expr e = parseExpr(c, tc.in);
        const Expr want = parseExpr(c, tc.expected);
        const Expr got = c.simplify(e);
        EXPECT_EQ(got, want)
            << "in:   " << tc.in << "\n  got:  " << c.toString(got)
            << "\n  want: " << c.toString(want);
    }
}

TEST(SimplifyTest, SpecialAngleTrigAndInverseTrigEvaluation)
{
    Ctx c;
    struct Case {
        const char *in;
        const char *expected;
    };
    const Case cases[] = {
        {"sin(pi/6)", "1/2"},
        {"sin(pi/4)", "2^(-1/2)"},
        {"sin(pi/3)", "1/2*3^(1/2)"},
        {"sin(pi/2)", "1"},
        {"sin(pi)", "0"},
        {"sin(7*pi/6)", "-1/2"},
        {"cos(pi/6)", "1/2*3^(1/2)"},
        {"cos(pi/4)", "2^(-1/2)"},
        {"cos(pi/3)", "1/2"},
        {"cos(pi/2)", "0"},
        {"cos(pi)", "-1"},
        {"cos(2*pi)", "1"},
        {"tan(pi/6)", "3^(-1/2)"},
        {"tan(pi/4)", "1"},
        {"tan(pi/3)", "3^(1/2)"},
        {"tan(pi)", "0"},
        {"cot(pi/4)", "1"},
        {"sec(pi/3)", "2"},
        {"csc(pi/6)", "2"},
        {"asin(1/2)", "1/6*pi"},
        {"asin(-1/2)", "-1/6*pi"},
        {"asin(1)", "1/2*pi"},
        {"asin(-1)", "-1/2*pi"},
        {"acos(1/2)", "1/3*pi"},
        {"acos(0)", "1/2*pi"},
        {"acos(-1)", "pi"},
        {"atan(1)", "1/4*pi"},
        {"atan(-1)", "-1/4*pi"},
        {"atan(3^(1/2))", "1/3*pi"},
        {"atan(3^(-1/2))", "1/6*pi"},
        {"acot(1)", "1/4*pi"},
        {"acot(0)", "1/2*pi"},
    };

    for (const auto &tc : cases) {
        const Expr e = parseExpr(c, tc.in);
        const Expr want = parseExpr(c, tc.expected);
        const Expr got = c.simplify(e);
        EXPECT_EQ(got, want)
            << "in:   " << tc.in << "\n  got:  " << c.toString(got)
            << "\n  want: " << c.toString(want);
    }
}

TEST(SimplifyTest, RationalGcdAndFactorization)
{
    Ctx c;
    struct Case {
        const char *in;
        const char *expected;
    };
    const Case cases[] = {
        {"(x^2 - 1)/(x - 1)", "1 + x"},
        {"(x^3 - 1)/(x - 1)", "1 + x + x^2"},
        {"x/(x + y) + y/(x + y)", "1"},
        {"1 + 2*x + x^2", "(1 + x)^2"},
        {"(x^2 + 2*x + 1)/(x + 1)", "1 + x"},
    };

    for (const auto &tc : cases) {
        const Expr e = parseExpr(c, tc.in);
        const Expr want = parseExpr(c, tc.expected);
        const Expr got = c.simplify(e);
        EXPECT_EQ(got, want)
            << "in:   " << tc.in << "\n  got:  " << c.toString(got)
            << "\n  want: " << c.toString(want);
    }
}

// ============================================================================
// Layer 2: Property Tests
// ============================================================================

TEST(SimplifyTest, PropertyZeroIdentitiesAndCostMonotonicity)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr sin2 = c.pow(c.func("sin", x), c.number(std::int64_t{2}));
    const Expr cos2 = c.pow(c.func("cos", x), c.number(std::int64_t{2}));
    const Expr sinh2 = c.pow(c.func("sinh", x), c.number(std::int64_t{2}));
    const Expr cosh2 = c.pow(c.func("cosh", x), c.number(std::int64_t{2}));

    std::mt19937 rng(0x514911F1u);
    std::uniform_int_distribution<int> cDist(-10, 10);

    for (int iter = 0; iter < 150; ++iter) {
        const int a0 = cDist(rng);
        int a1 = cDist(rng);
        if (a1 == 0)
            a1 = 1;
        const int b0 = cDist(rng);
        int b1 = cDist(rng);
        if (b1 == 0)
            b1 = 2;

        const Expr P = c.add({c.number(static_cast<std::int64_t>(a0)),
                              c.mul({c.number(static_cast<std::int64_t>(a1)), x})});
        const Expr Q = c.add({c.number(static_cast<std::int64_t>(b0)),
                              c.mul({c.number(static_cast<std::int64_t>(b1)), x})});

        // 1. (P * Q) / Q - P == 0
        const Expr ratId = c.add({c.div(c.expand(c.mul({P, Q})), Q), c.neg(P)});
        EXPECT_EQ(c.simplify(ratId), c.zero()) << "iter " << iter;

        // 2. P * sin(x)^2 + P * cos(x)^2 - P == 0
        const Expr trigId =
            c.add({c.mul({P, sin2}), c.mul({P, cos2}), c.neg(P)});
        EXPECT_EQ(c.simplify(trigId), c.zero()) << "iter " << iter;

        // 3. P * cosh(x)^2 - P * sinh(x)^2 - P == 0
        const Expr hypId =
            c.add({c.mul({P, cosh2}), c.neg(c.mul({P, sinh2})), c.neg(P)});
        EXPECT_EQ(c.simplify(hypId), c.zero()) << "iter " << iter;

        // 4. Cost monotonicity and numerical preservation on expanded (P * Q) / Q
        const Expr unsimplified = c.div(c.expand(c.mul({P, Q})), Q);
        const Expr simp = c.simplify(unsimplified);
        EXPECT_LE(c.exprCost(simp), c.exprCost(unsimplified));
        EXPECT_EQ(c.simplify(simp), simp); // idempotent
        double v1 = 0.0, v2 = 0.0;
        ASSERT_TRUE(c.evalDouble(unsimplified, {{"x", 0.37}}, v1));
        ASSERT_TRUE(c.evalDouble(simp, {{"x", 0.37}}, v2));
        EXPECT_NEAR(v1, v2, 1e-12);
    }
}

// ============================================================================
// Layer 3: Boundary Tests
// ============================================================================

TEST(SimplifyTest, BoundaryCases)
{
    Ctx c;
    EXPECT_TRUE(c.simplify(Expr()).isNull());
    EXPECT_EQ(c.simplify(c.zero()), c.zero());
    EXPECT_EQ(c.simplify(c.one()), c.one());
    const Expr x = c.symbol("x");
    EXPECT_EQ(c.simplify(x), x);

    Budget exhausted(0);
    const Expr e = parseExpr(c, "sin(x)^2 + cos(x)^2");
    EXPECT_EQ(simplify(c, e, &exhausted), e);
    EXPECT_EQ(exhausted.status(), BudgetStatus::StepExhausted);
}

TEST(SimplifyTest, AssumptionsInferenceAndSimplification)
{
    Ctx c;
    const Expr u = c.symbol("u");
    const Expr v = c.symbol("v");
    const Expr x = c.symbol("x");
    const Expr n = c.symbol("n");
    const Expr a = c.symbol("a");
    const Expr b = c.symbol("b");

    // Unconstrained symbols do not trigger domain-restricted identities
    EXPECT_EQ(c.simplify(parseExpr(c, "sqrt(u^2)")), parseExpr(c, "(u^2)^(1/2)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "log(u^2)")), parseExpr(c, "log(u^2)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "sin(n*pi)")), parseExpr(c, "sin(n*pi)"));

    c.assume(u, AssumeDomain::Positive);
    c.assume(v, AssumeDomain::Negative);
    c.assume(x, AssumeDomain::Real);
    c.assume(n, AssumeDomain::Integer);
    c.assume(a, AssumeDomain::Real);
    c.assume(b, AssumeDomain::Real);

    // Expression-level inference predicates
    EXPECT_TRUE(c.isAssumedPositive(u));
    EXPECT_TRUE(c.isAssumedNegative(v));
    EXPECT_TRUE(c.isAssumedPositive(c.mul({v, v})));
    EXPECT_TRUE(c.isAssumedNegative(c.mul({u, v})));
    EXPECT_TRUE(c.isAssumedNonNegative(parseExpr(c, "x^2")));
    EXPECT_TRUE(c.isAssumedPositive(parseExpr(c, "1 + x^2")));
    EXPECT_TRUE(c.isAssumedPositive(parseExpr(c, "exp(x)")));
    EXPECT_TRUE(c.isAssumedPositive(parseExpr(c, "cosh(x)")));
    EXPECT_TRUE(c.isAssumedInteger(parseExpr(c, "3*n^2 - 2*n + 5")));

    // Positive assumptions
    EXPECT_EQ(c.simplify(parseExpr(c, "sqrt(u^2)")), u);
    EXPECT_EQ(c.simplify(parseExpr(c, "sqrt(4*u^2*y)")),
              parseExpr(c, "2*u*y^(1/2)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "log(u^2)")), parseExpr(c, "2*log(u)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "log(u^a)")), parseExpr(c, "a*log(u)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "(u^a)^b")), parseExpr(c, "u^(a*b)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "abs(u)")), u);
    EXPECT_EQ(c.simplify(parseExpr(c, "acosh(cosh(u))")), u);

    // Negative assumptions
    EXPECT_EQ(c.simplify(parseExpr(c, "sqrt(v^2)")), c.neg(v));
    EXPECT_EQ(c.simplify(parseExpr(c, "sqrt(9*v^2*y)")),
              parseExpr(c, "-3*v*y^(1/2)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "abs(v)")), c.neg(v));
    EXPECT_EQ(c.simplify(parseExpr(c, "acosh(cosh(v))")), c.neg(v));

    // Real assumptions and composite positive expressions (1 + x^2 > 0)
    EXPECT_EQ(c.simplify(parseExpr(c, "sqrt((1 + x^2)^2)")),
              parseExpr(c, "1 + x^2"));
    EXPECT_EQ(c.simplify(parseExpr(c, "log((1 + x^2)^2)")),
              parseExpr(c, "2*log(1 + x^2)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "asinh(sinh(x))")), x);
    EXPECT_EQ(c.simplify(parseExpr(c, "atanh(tanh(x))")), x);

    // Integer assumptions
    EXPECT_EQ(c.simplify(parseExpr(c, "sin(n*pi)")), c.zero());
    EXPECT_EQ(c.simplify(parseExpr(c, "tan(n*pi)")), c.zero());
    EXPECT_EQ(c.simplify(parseExpr(c, "cos(2*n*pi)")), c.one());
    EXPECT_EQ(c.simplify(parseExpr(c, "cos(n*pi)")), parseExpr(c, "(-1)^n"));
    EXPECT_EQ(c.simplify(parseExpr(c, "(-1)^(2*n)")), c.one());

    // Clearing assumptions restores unconstrained behavior
    c.clearAssumptions();
    EXPECT_EQ(c.assumption(u), AssumeDomain::Any);
    EXPECT_EQ(c.simplify(parseExpr(c, "sqrt(u^2)")), parseExpr(c, "(u^2)^(1/2)"));
}

TEST(SimplifyTest, GammaDigammaTrigammaIdentitiesAndEvaluation)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // 1. Exact integer and half-integer values of gamma and lgamma
    EXPECT_EQ(c.simplify(parseExpr(c, "gamma(1)")), c.one());
    EXPECT_EQ(c.simplify(parseExpr(c, "gamma(5)")), c.number(24));
    EXPECT_EQ(c.simplify(parseExpr(c, "gamma(1/2)")),
              c.simplify(parseExpr(c, "sqrt(pi)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "gamma(5/2)")),
              c.simplify(parseExpr(c, "(3/4)*sqrt(pi)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "gamma(-1/2)")),
              c.simplify(parseExpr(c, "-2*sqrt(pi)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "lgamma(1)")), c.zero());
    EXPECT_EQ(c.simplify(parseExpr(c, "loggamma(2)")), c.zero());
    EXPECT_EQ(c.simplify(parseExpr(c, "lgamma(4)")),
              c.simplify(parseExpr(c, "log(6)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "lgamma(1/2)")),
              c.simplify(parseExpr(c, "(1/2)*log(pi)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "exp(lgamma(x))")),
              parseExpr(c, "gamma(x)"));

    // 2. Exact values of digamma (psi) and trigamma
    EXPECT_EQ(c.simplify(parseExpr(c, "psi(1)")),
              parseExpr(c, "-euler_gamma"));
    EXPECT_EQ(c.simplify(parseExpr(c, "digamma(4)")),
              c.simplify(parseExpr(c, "11/6 - euler_gamma")));
    EXPECT_EQ(c.simplify(parseExpr(c, "digamma(1/2)")),
              c.simplify(parseExpr(c, "-euler_gamma - 2*log(2)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "digamma(3/2)")),
              c.simplify(parseExpr(c, "2 - euler_gamma - 2*log(2)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "digamma(1/4)")),
              c.simplify(parseExpr(c, "-euler_gamma - pi/2 - 3*log(2)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "digamma(3/4)")),
              c.simplify(parseExpr(c, "-euler_gamma + pi/2 - 3*log(2)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "trigamma(1)")),
              c.simplify(parseExpr(c, "pi^2/6")));
    EXPECT_EQ(c.simplify(parseExpr(c, "trigamma(3)")),
              c.simplify(parseExpr(c, "pi^2/6 - 5/4")));
    EXPECT_EQ(c.simplify(parseExpr(c, "trigamma(1/2)")),
              c.simplify(parseExpr(c, "pi^2/2")));

    // 3. Gamma integer-shift ratio, Euler reflection, and polygamma recurrences
    EXPECT_EQ(c.simplify(parseExpr(c, "gamma(x + 2)/gamma(x)")),
              c.simplify(parseExpr(c, "x*(x + 1)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "gamma(1/3)*gamma(2/3)")),
              c.simplify(parseExpr(c, "2*3^(-1/2)*pi")));
    EXPECT_EQ(c.simplify(parseExpr(c, "gamma(1/4)*gamma(3/4)")),
              c.simplify(parseExpr(c, "sqrt(2)*pi")));
    EXPECT_EQ(c.simplify(parseExpr(c, "digamma(x + 2) - digamma(x)")),
              c.simplify(parseExpr(c, "1/x + 1/(x + 1)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "trigamma(x + 1) - trigamma(x)")),
              c.simplify(parseExpr(c, "-1/x^2")));

    // 4. Derivatives and IEEE-754 double evaluation
    EXPECT_EQ(c.simplify(c.diff(parseExpr(c, "gamma(x^2)"), x)),
              c.simplify(parseExpr(c, "2*x*gamma(x^2)*digamma(x^2)")));
    EXPECT_EQ(c.simplify(c.diff(parseExpr(c, "lgamma(x)"), x)),
              parseExpr(c, "digamma(x)"));
    EXPECT_EQ(c.simplify(c.diff(parseExpr(c, "digamma(x)"), x)),
              parseExpr(c, "trigamma(x)"));

    double vPsi = 0.0, vTri = 0.0, vEG = 0.0;
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "euler_gamma"), {}, vEG));
    EXPECT_NEAR(vEG, 0.57721566490153286, 1e-15);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "digamma(1)"), {}, vPsi));
    EXPECT_NEAR(vPsi, -vEG, 1e-14);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "trigamma(1)"), {}, vTri));
    EXPECT_NEAR(vTri, 3.14159265358979323846 * 3.14159265358979323846 / 6.0,
                1e-14);
}

TEST(SimplifyTest, OrthogonalPolynomialsBesselAndAiryIdentities)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // 1. Explicit expansion of classical orthogonal polynomials
    EXPECT_EQ(c.simplify(parseExpr(c, "legendreP(3, x)")),
              c.simplify(parseExpr(c, "5/2*x^3 - 3/2*x")));
    EXPECT_EQ(c.simplify(parseExpr(c, "chebyshevT(4, x)")),
              c.simplify(parseExpr(c, "8*x^4 - 8*x^2 + 1")));
    EXPECT_EQ(c.simplify(parseExpr(c, "chebyshevU(3, x)")),
              c.simplify(parseExpr(c, "8*x^3 - 4*x")));
    EXPECT_EQ(c.simplify(parseExpr(c, "hermiteH(3, x)")),
              c.simplify(parseExpr(c, "8*x^3 - 12*x")));
    EXPECT_EQ(c.simplify(parseExpr(c, "laguerreL(2, x)")),
              c.simplify(parseExpr(c, "1/2*x^2 - 2*x + 1")));

    // 2. Symbolic-degree identities and three-term recurrences
    EXPECT_EQ(c.simplify(parseExpr(c, "chebyshevT(n, cos(x))")),
              parseExpr(c, "cos(n*x)"));
    EXPECT_EQ(c.simplify(parseExpr(
                  c, "(n + 1)*legendreP(n + 1, x) - (2*n + 1)*x*legendreP(n, x) + n*legendreP(n - 1, x)")),
              c.zero());
    EXPECT_EQ(c.simplify(parseExpr(
                  c, "hermiteH(n + 1, x) - 2*x*hermiteH(n, x) + 2*n*hermiteH(n - 1, x)")),
              c.zero());

    // 3. Half-integer Bessel functions and 3-term recurrence / ODE verification
    EXPECT_EQ(c.simplify(parseExpr(c, "besselj(1/2, x)")),
              c.simplify(parseExpr(c, "2^(1/2)*pi^(-1/2)*x^(-1/2)*sin(x)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "besselj(-1/2, x)")),
              c.simplify(parseExpr(c, "2^(1/2)*pi^(-1/2)*x^(-1/2)*cos(x)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "besseli(1/2, x)")),
              c.simplify(parseExpr(c, "2^(1/2)*pi^(-1/2)*x^(-1/2)*sinh(x)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "besselk(1/2, x)")),
              c.simplify(parseExpr(c, "2^(-1/2)*pi^(1/2)*x^(-1/2)*exp(-x)")));

    EXPECT_EQ(c.simplify(parseExpr(
                  c, "besselj(nu - 1, x) + besselj(nu + 1, x) - 2*nu/x*besselj(nu, x)")),
              c.zero());

    // Bessel's differential equation: x^2*y'' + x*y' + (x^2 - nu^2)*y = 0
    const Expr jNu = parseExpr(c, "besselj(nu, x)");
    const Expr djNu = c.diff(jNu, x);
    const Expr ddjNu = c.diff(djNu, x);
    const Expr besselOdeRes = c.simplify(c.add({
        c.mul({c.pow(x, c.number(2)), ddjNu}),
        c.mul({x, djNu}),
        c.mul({parseExpr(c, "x^2 - nu^2"), jNu})}));
    EXPECT_EQ(besselOdeRes, c.zero());

    // Airy's differential equation: y'' - x*y = 0
    const Expr ai = parseExpr(c, "airyAi(x)");
    EXPECT_EQ(c.simplify(c.add({c.diff(c.diff(ai, x), x), c.neg(c.mul({x, ai}))})),
              c.zero());

    // 4. IEEE-754 double evaluation
    double j0At0 = 0.0, j0At1 = 0.0, aiAt0 = 0.0;
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "besselj(0, 0)"), {}, j0At0));
    EXPECT_DOUBLE_EQ(j0At0, 1.0);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "besselj(0, 1)"), {}, j0At1));
    EXPECT_NEAR(j0At1, 0.76519768655796655, 1e-14);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "airyAi(0)"), {}, aiAt0));
    EXPECT_NEAR(aiAt0, 0.35502805388781724, 1e-14);
}

TEST(SimplifyTest, EllipticIntegralsAndLegendreIdentity)
{
    Ctx c;
    const Expr m = c.symbol("m");
    const Expr phi = c.symbol("phi");

    // 1. Special values and reductions
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticK(0)")),
              c.simplify(parseExpr(c, "1/2*pi")));
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticE(0)")),
              c.simplify(parseExpr(c, "1/2*pi")));
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticE(1)")), c.one());
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticPi(0, m)")),
              parseExpr(c, "ellipticK(m)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticPi(n, 0)")),
              c.simplify(parseExpr(c, "1/2*pi*(1 - n)^(-1/2)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticPi(m, m)")),
              c.simplify(parseExpr(c, "(1 - m)^(-1)*ellipticE(m)")));

    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticF(0, m)")), c.zero());
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticF(phi, 0)")), phi);
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticEInc(0, m)")), c.zero());
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticEInc(phi, 0)")), phi);
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticF(1/2*pi, m)")),
              parseExpr(c, "ellipticK(m)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticEInc(1/2*pi, m)")),
              parseExpr(c, "ellipticE(m)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticF(pi, m)")),
              c.simplify(parseExpr(c, "2*ellipticK(m)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticEInc(pi, m)")),
              c.simplify(parseExpr(c, "2*ellipticE(m)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "ellipticF(-phi, m) + ellipticF(phi, m)")),
              c.zero());

    // 2. Legendre's complete elliptic integral identity:
    //    E(m)*K(1-m) + E(1-m)*K(m) - K(m)*K(1-m) = pi/2
    EXPECT_EQ(c.simplify(parseExpr(
                  c, "ellipticE(m)*ellipticK(1 - m) + ellipticE(1 - m)*ellipticK(m) - ellipticK(m)*ellipticK(1 - m)")),
              c.simplify(parseExpr(c, "1/2*pi")));
    EXPECT_EQ(c.simplify(parseExpr(
                  c, "2*ellipticE(1/2)*ellipticK(1/2) - ellipticK(1/2)^2")),
              c.simplify(parseExpr(c, "1/2*pi")));

    // 3. Complete elliptic differential equations for K(m) and E(m):
    //    m*(1-m)*K''(m) + (1-2*m)*K'(m) - 1/4*K(m) = 0
    //    m*(1-m)*E''(m) + (1-m)*E'(m) + 1/4*E(m) = 0
    const Expr km = parseExpr(c, "ellipticK(m)");
    const Expr dkm = c.diff(km, m);
    const Expr ddkm = c.diff(dkm, m);
    EXPECT_EQ(c.simplify(c.add({
                  c.mul({parseExpr(c, "m*(1 - m)"), ddkm}),
                  c.mul({parseExpr(c, "1 - 2*m"), dkm}),
                  c.mul({parseExpr(c, "-1/4"), km})})),
              c.zero());

    const Expr em = parseExpr(c, "ellipticE(m)");
    const Expr dem = c.diff(em, m);
    const Expr ddem = c.diff(dem, m);
    EXPECT_EQ(c.simplify(c.add({
                  c.mul({parseExpr(c, "m*(1 - m)"), ddem}),
                  c.mul({parseExpr(c, "1 - m"), dem}),
                  c.mul({parseExpr(c, "1/4"), em})})),
              c.zero());

    // 4. Carlson symmetric form IEEE-754 double evaluation
    double kHalf = 0.0, eHalf = 0.0, piVal = 0.0, fInc = 0.0, eInc = 0.0;
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "ellipticK(1/2)"), {}, kHalf));
    EXPECT_NEAR(kHalf, 1.8540746773013719, 1e-14);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "ellipticE(1/2)"), {}, eHalf));
    EXPECT_NEAR(eHalf, 1.3506438810476755, 1e-14);
    EXPECT_NEAR(2.0 * eHalf * kHalf - kHalf * kHalf,
                3.14159265358979323846 / 2.0, 1e-14);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "ellipticPi(1/3, 1/2)"), {}, piVal));
    EXPECT_NEAR(piVal, 2.3107949907542817, 1e-14);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "ellipticF(1/3*pi, 1/2)"), {}, fInc));
    EXPECT_NEAR(fInc, 1.1424290580457772, 1e-14);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "ellipticEInc(1/3*pi, 1/2)"), {}, eInc));
    EXPECT_NEAR(eInc, 0.9649514576429924, 1e-14);
}

TEST(SimplifyTest, ZetaDirichletEtaPolylogAndBernoulliEuler)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr s = c.symbol("s");
    const Expr n = c.symbol("n");

    // 1. Exact Bernoulli & Euler numbers and polynomials
    EXPECT_EQ(c.simplify(parseExpr(c, "bernoulliB(0)")), c.one());
    EXPECT_EQ(c.simplify(parseExpr(c, "bernoulliB(1)")),
              parseExpr(c, "-1/2"));
    EXPECT_EQ(c.simplify(parseExpr(c, "bernoulliB(2)")),
              parseExpr(c, "1/6"));
    EXPECT_EQ(c.simplify(parseExpr(c, "bernoulliB(4)")),
              parseExpr(c, "-1/30"));
    EXPECT_EQ(c.simplify(parseExpr(c, "bernoulliB(12)")),
              parseExpr(c, "-691/2730"));
    EXPECT_EQ(c.simplify(parseExpr(c, "eulerE(0)")), c.one());
    EXPECT_EQ(c.simplify(parseExpr(c, "eulerE(2)")), c.number(-1));
    EXPECT_EQ(c.simplify(parseExpr(c, "eulerE(4)")), c.number(5));
    EXPECT_EQ(c.simplify(parseExpr(c, "eulerE(6)")), c.number(-61));

    // Polynomial expansion of bernoulliB(n, x) and eulerE(n, x)
    EXPECT_EQ(c.simplify(c.expand(parseExpr(c, "bernoulliB(3, x)"))),
              c.simplify(parseExpr(c, "x^3 - 3/2*x^2 + 1/2*x")));
    EXPECT_EQ(c.simplify(c.expand(parseExpr(c, "eulerE(3, x)"))),
              c.simplify(parseExpr(c, "x^3 - 3/2*x^2 + 1/4")));

    // Shift and derivative identities for symbolic n:
    //   bernoulliB(n, x + 1) - bernoulliB(n, x) = n*x^(n - 1)
    //   eulerE(n, x + 1) + eulerE(n, x)         = 2*x^n
    EXPECT_EQ(c.simplify(parseExpr(
                  c, "bernoulliB(n, x + 1) - bernoulliB(n, x) - n*x^(n - 1)")),
              c.zero());
    EXPECT_EQ(c.simplify(parseExpr(
                  c, "eulerE(n, x + 1) + eulerE(n, x) - 2*x^n")),
              c.zero());
    EXPECT_EQ(c.simplify(c.diff(parseExpr(c, "bernoulliB(n, x)"), x)),
              c.simplify(parseExpr(c, "n*bernoulliB(n - 1, x)")));
    EXPECT_EQ(c.simplify(c.diff(parseExpr(c, "eulerE(n, x)"), x)),
              c.simplify(parseExpr(c, "n*eulerE(n - 1, x)")));

    // 2. Exact values of zeta(s) and dirichletEta(s)
    EXPECT_EQ(c.simplify(parseExpr(c, "zeta(0)")), parseExpr(c, "-1/2"));
    EXPECT_EQ(c.simplify(parseExpr(c, "zeta(-1)")), parseExpr(c, "-1/12"));
    EXPECT_EQ(c.simplify(parseExpr(c, "zeta(-2)")), c.zero());
    EXPECT_EQ(c.simplify(parseExpr(c, "zeta(-3)")), parseExpr(c, "1/120"));
    EXPECT_EQ(c.simplify(parseExpr(c, "zeta(2)")),
              c.simplify(parseExpr(c, "1/6*pi^2")));
    EXPECT_EQ(c.simplify(parseExpr(c, "zeta(4)")),
              c.simplify(parseExpr(c, "1/90*pi^4")));
    EXPECT_EQ(c.simplify(parseExpr(c, "zeta(6)")),
              c.simplify(parseExpr(c, "1/945*pi^6")));
    EXPECT_EQ(c.simplify(parseExpr(c, "dirichletEta(1)")),
              parseExpr(c, "log(2)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "dirichletEta(2)")),
              c.simplify(parseExpr(c, "1/12*pi^2")));
    EXPECT_EQ(c.simplify(parseExpr(c, "dirichletEta(3)")),
              c.simplify(parseExpr(c, "3/4*zeta(3)")));
    EXPECT_EQ(c.simplify(parseExpr(
                  c, "dirichletEta(s) - (1 - 2^(1 - s))*zeta(s)")),
              c.zero());

    // 3. Polylogarithm reductions and differentiation
    EXPECT_EQ(c.simplify(parseExpr(c, "polylog(2, x)")),
              parseExpr(c, "dilog(x)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "polylog(1, x)")),
              c.simplify(parseExpr(c, "-log(1 - x)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "polylog(0, x)")),
              c.simplify(parseExpr(c, "x*(1 - x)^(-1)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "polylog(-1, x)")),
              c.simplify(parseExpr(c, "x*(1 - x)^(-2)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "polylog(-2, x)")),
              c.simplify(parseExpr(c, "x*(1 + x)*(1 - x)^(-3)")));
    EXPECT_EQ(c.simplify(parseExpr(c, "polylog(3, 1)")),
              parseExpr(c, "zeta(3)"));
    EXPECT_EQ(c.simplify(parseExpr(c, "polylog(3, -1)")),
              c.simplify(parseExpr(c, "-3/4*zeta(3)")));
    EXPECT_EQ(c.simplify(c.diff(parseExpr(c, "polylog(4, x)"), x)),
              c.simplify(parseExpr(c, "x^(-1)*polylog(3, x)")));

    // 4. IEEE-754 double evaluation of zeta, dirichletEta, polylog
    double z3 = 0.0, eta3 = 0.0, li3Half = 0.0;
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "zeta(3)"), {}, z3));
    EXPECT_NEAR(z3, 1.2020569031595942, 1e-13);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "dirichletEta(3)"), {}, eta3));
    EXPECT_NEAR(eta3, 0.9015426773696957, 1e-13);
    ASSERT_TRUE(c.evalDouble(parseExpr(c, "polylog(3, 1/2)"), {}, li3Half));
    EXPECT_NEAR(li3Half, 0.5372131936080402, 1e-14);
}

} // namespace
} // namespace numkit::cas
