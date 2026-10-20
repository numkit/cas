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

} // namespace
} // namespace numkit::cas
