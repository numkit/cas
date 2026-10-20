#include <numkit/cas/transform/laplace.hpp>

#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <random>
#include <vector>

namespace numkit::cas {
namespace {

bool equivExpr(Ctx &c, Expr a, Expr b)
{
    if (a.isNull() || b.isNull())
        return a.isNull() && b.isNull();
    const Expr d = c.add({a, c.neg(b)});
    if (c.isZero(d))
        return true;
    if (c.isZero(simplifyRationalExpr(c, d)))
        return true;
    const Expr sd = c.simplify(d);
    if (c.isZero(sd))
        return true;
    return c.isZero(simplifyRationalExpr(c, sd));
}

// ============================================================================
// Layer 1: Fixed Oracle Vectors
// ============================================================================

TEST(LaplaceTest, ForwardLaplaceFixedVectors)
{
    Ctx c;
    const Expr t = c.symbol("t");
    const Expr s = c.symbol("s");

    struct Case {
        const char *f;
        const char *expected;
    };
    const Case cases[] = {
        {"1", "1/s"},
        {"5", "5/s"},
        {"t", "1/s^2"},
        {"t^4", "24/s^5"},
        {"t^(-1/2)", "pi^(1/2)*s^(-1/2)"},
        {"t^(1/2)", "1/2*pi^(1/2)*s^(-3/2)"},
        {"t^(3/2)", "3/4*pi^(1/2)*s^(-5/2)"},
        {"exp(a*t)", "1/(s - a)"},
        {"t^2*exp(-3*t)", "2/(s + 3)^3"},
        {"sin(w*t)", "w/(s^2 + w^2)"},
        {"cos(w*t)", "s/(s^2 + w^2)"},
        {"sinh(a*t)", "a/(s^2 - a^2)"},
        {"cosh(a*t)", "s/(s^2 - a^2)"},
        {"exp(-2*t)*sin(3*t)", "3/((s + 2)^2 + 9)"},
        {"exp(-2*t)*cos(3*t)", "(s + 2)/((s + 2)^2 + 9)"},
        {"t*sin(w*t)", "2*w*s/(s^2 + w^2)^2"},
        {"t*cos(w*t)", "(s^2 - w^2)/(s^2 + w^2)^2"},
        {"t*sinh(a*t)", "2*a*s/(s^2 - a^2)^2"},
        {"sin(w*t)^2", "2*w^2/(s*(s^2 + 4*w^2))"},
        {"cos(w*t)^2", "(s^2 + 2*w^2)/(s*(s^2 + 4*w^2))"},
        {"sin(3*t)*cos(t)", "3*(s^2 + 8)/((s^2 + 4)*(s^2 + 16))"},
        {"sinh(a*t)^2", "2*a^2/(s*(s^2 - 4*a^2))"},
    };

    for (const auto &tc : cases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr want = parseExpr(c, tc.expected);
        const LaplaceResult r = laplace(c, f, t, s);
        ASSERT_TRUE(r.proved()) << "f = " << tc.f << ": " << r.reason;
        EXPECT_TRUE(equivExpr(c, r.F, want))
            << "f = " << tc.f << "\n  got:  " << c.toString(r.F)
            << "\n  want: " << c.toString(want);
    }
}

TEST(LaplaceTest, InverseLaplaceFixedVectors)
{
    Ctx c;
    const Expr s = c.symbol("s");
    const Expr t = c.symbol("t");

    struct Case {
        const char *F;
        const char *expected;
    };
    const Case cases[] = {
        {"1/s", "1"},
        {"6/s^4", "t^3"},
        {"1/(s - 3)", "exp(3*t)"},
        {"2/(s + 2)^3", "t^2*exp(-2*t)"},
        {"1/((s + 1)*(s + 2))", "exp(-t) - exp(-2*t)"},
        {"(s + 3)/((s + 1)*(s + 2)^2)", "2*exp(-t) - 2*exp(-2*t) - t*exp(-2*t)"},
        {"3/(s^2 + 9)", "sin(3*t)"},
        {"s/(s^2 + 4)", "cos(2*t)"},
        {"(s + 1)/(s^2 + 2*s + 5)", "exp(-t)*cos(2*t)"},
        {"2/(s^2 + 2*s + 5)", "exp(-t)*sin(2*t)"},
        {"1/(s^2 + 2)", "2^(-1/2)*sin(2^(1/2)*t)"},
        {"2*s/(s^2 + 1)^2", "t*sin(t)"},
        {"2/(s^2 + 1)^2", "sin(t) - t*cos(t)"},
        {"1/(s^2 - 9)", "1/6*exp(3*t) - 1/6*exp(-3*t)"},
        // Parametric symbolic forms
        {"1/(s - a)", "exp(a*t)"},
        {"2/(s + a)^3", "t^2*exp(-a*t)"},
        {"w/(s^2 + w^2)", "sin(w*t)"},
        {"s/(s^2 + w^2)", "cos(w*t)"},
        {"s^(-1/2)", "pi^(-1/2)*t^(-1/2)"},
        {"s^(-3/2)", "2*pi^(-1/2)*t^(1/2)"},
    };

    for (const auto &tc : cases) {
        const Expr F = parseExpr(c, tc.F);
        const Expr want = parseExpr(c, tc.expected);
        const LaplaceResult r = ilaplace(c, F, s, t);
        ASSERT_TRUE(r.proved()) << "F = " << tc.F << ": " << r.reason;
        // Both r.F and want must have identical Laplace transform F(s), and
        // simplify(r.F - want) == 0.
        const LaplaceResult fwdGot = laplace(c, r.F, t, s);
        ASSERT_TRUE(fwdGot.proved());
        EXPECT_TRUE(equivExpr(c, fwdGot.F, F))
            << "F = " << tc.F << "\n  got f(t): " << c.toString(r.F);
    }
}

// ============================================================================
// Layer 2: Property Tests
// ============================================================================

TEST(LaplaceTest, PropertyLaplaceIlaplaceRoundTrip)
{
    Ctx c;
    const Expr t = c.symbol("t");
    const Expr s = c.symbol("s");
    std::mt19937 rng(0x1A91ACE1u);
    std::uniform_int_distribution<int> coeffDist(-5, 5);
    std::uniform_int_distribution<int> poleDist(-4, 4);
    std::uniform_int_distribution<int> freqDist(1, 4);
    std::uniform_int_distribution<int> degDist(0, 2);

    for (int iter = 0; iter < 80; ++iter) {
        const int c1 = coeffDist(rng) == 0 ? 1 : coeffDist(rng);
        const int c2 = coeffDist(rng) == 0 ? -2 : coeffDist(rng);
        const int r1 = poleDist(rng);
        const int alpha = poleDist(rng);
        const int w = freqDist(rng);
        const int d = degDist(rng);

        // f(t) = c1 * t^d * exp(r1*t) + c2 * exp(alpha*t) * cos(w*t)
        const Expr term1 = c.mul(
            {c.number(static_cast<std::int64_t>(c1)),
             c.pow(t, c.number(static_cast<std::int64_t>(d))),
             c.func("exp", c.mul({c.number(static_cast<std::int64_t>(r1)), t}))});
        const Expr term2 = c.mul(
            {c.number(static_cast<std::int64_t>(c2)),
             c.func("exp", c.mul({c.number(static_cast<std::int64_t>(alpha)), t})),
             c.func("cos", c.mul({c.number(static_cast<std::int64_t>(w)), t}))});
        const Expr f = c.add({term1, term2});

        const LaplaceResult fwd = laplace(c, f, t, s);
        ASSERT_TRUE(fwd.proved()) << "iter " << iter << ": " << fwd.reason;

        // Combine into a single rational function in s and invert via ilaplace
        const Expr F_rat = simplifyRationalExpr(c, fwd.F);
        const LaplaceResult inv = ilaplace(c, F_rat, s, t);
        ASSERT_TRUE(inv.proved())
            << "iter " << iter << " F_rat=" << c.toString(F_rat) << ": "
            << inv.reason;

        EXPECT_TRUE(equivExpr(c, inv.F, f))
            << "iter " << iter << "\n  orig: " << c.toString(f)
            << "\n  inv:  " << c.toString(inv.F);
    }
}

// ============================================================================
// Layer 3: Boundary Tests
// ============================================================================

TEST(LaplaceTest, BoundaryAndHonestDeclines)
{
    Ctx c;
    const Expr t = c.symbol("t");
    const Expr s = c.symbol("s");

    // Zero transforms to zero in both directions
    {
        const LaplaceResult fwd0 = laplace(c, c.zero(), t, s);
        ASSERT_TRUE(fwd0.proved());
        EXPECT_EQ(fwd0.F, c.zero());
        const LaplaceResult inv0 = ilaplace(c, c.zero(), s, t);
        ASSERT_TRUE(inv0.proved());
        EXPECT_EQ(inv0.F, c.zero());
    }

    // Improper rational functions in s (deg(N) >= deg(D)) decline in ilaplace
    {
        const LaplaceResult r1 = ilaplace(c, c.one(), s, t);
        EXPECT_FALSE(r1.proved());
        const LaplaceResult r2 =
            ilaplace(c, parseExpr(c, "s^2/(s^2 + 1)"), s, t);
        EXPECT_FALSE(r2.proved());
    }

    // Non-elementary / super-exponential functions decline in laplace
    {
        const LaplaceResult r = laplace(c, parseExpr(c, "exp(t^2)"), t, s);
        EXPECT_FALSE(r.proved());
    }

    // Budget exhaustion stops cleanly
    {
        Budget exhausted(0);
        const LaplaceResult r =
            laplace(c, parseExpr(c, "sin(t)"), t, s, &exhausted);
        EXPECT_FALSE(r.proved());
        EXPECT_EQ(exhausted.status(), BudgetStatus::StepExhausted);
    }
}

} // namespace
} // namespace numkit::cas
