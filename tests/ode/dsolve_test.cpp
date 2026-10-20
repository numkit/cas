#include <numkit/cas/ode/dsolve.hpp>

#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/core/simplify.hpp>

#include <gtest/gtest.h>

#include <cmath>
#include <random>
#include <string>

namespace numkit::cas {
namespace {

Expr P(Ctx &c, const std::string &s) { return parseExpr(c, s); }

bool checkOde1(Ctx &c, Expr ySol, Expr rhs, Expr x, Expr y)
{
    const Expr dy = c.diff(ySol, x);
    const Expr rhsSub = c.subs(rhs, y, ySol);
    const Expr res = c.simplify(c.add({dy, c.neg(rhsSub)}));
    return c.isZero(res);
}

bool checkOde2(Ctx &c, Expr ySol, Expr a, Expr b, Expr d, Expr f, Expr x)
{
    const Expr dy = c.diff(ySol, x);
    const Expr d2y = c.diff(dy, x);
    const Expr lhs = c.add({c.mul({a, d2y}), c.mul({b, dy}), c.mul({d, ySol})});
    const Expr res = c.simplify(c.add({lhs, c.neg(f)}));
    return c.isZero(res);
}

bool sameExpr(Ctx &c, Expr a, Expr b)
{
    return c.isZero(c.simplify(c.add({a, c.neg(b)})));
}

// ============================================================================
// Layer 1: Fixed oracle vectors
// ============================================================================

TEST(DsolveTest, FirstOrderQuadratureAndLinear)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");

    // 1. Pure quadrature: y' = 3*x^2 - 2*x + 1 -> y = x^3 - x^2 + x + C1
    {
        const Expr rhs = P(c, "3*x^2 - 2*x + 1");
        const OdeResult sol = dsolve1(c, rhs, x, y);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde1(c, sol.y, rhs, x, y));
        EXPECT_TRUE(sameExpr(c, sol.y, P(c, "x^3 - x^2 + x + C1")));
    }

    // 2. Constant-coefficient linear: y' = -2*y + 4 -> y = 2 + C1 * exp(-2*x)
    {
        const Expr rhs = P(c, "-2*y + 4");
        const OdeResult sol = dsolve1(c, rhs, x, y);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde1(c, sol.y, rhs, x, y));
    }

    // 3. Linear with exponential forcing: y' = -3*y + exp(-x)
    {
        const Expr rhs = P(c, "-3*y + exp(-x)");
        const OdeResult sol = dsolve1(c, rhs, x, y);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde1(c, sol.y, rhs, x, y));
    }

    // 4. Variable-coefficient linear: y' = (2/x)*y + x^3
    // Integrating factor mu = x^-2 -> d/dx(y/x^2) = x -> y = x^4/2 + C1*x^2
    {
        const Expr rhs = P(c, "(2/x)*y + x^3");
        const OdeResult sol = dsolve1(c, rhs, x, y);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde1(c, sol.y, rhs, x, y));
        EXPECT_TRUE(sameExpr(c, sol.y, P(c, "1/2*x^4 + C1*x^2")));
    }
}

TEST(DsolveTest, FirstOrderSeparableAndBernoulli)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");

    // 1. Separable: y' = x * y^2 -> -1/y = x^2/2 + C1 -> y = -1 / (x^2/2 + C1)
    {
        const Expr rhs = P(c, "x * y^2");
        const OdeResult sol = dsolve1(c, rhs, x, y);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde1(c, sol.y, rhs, x, y));
    }

    // 2. Separable: y' = (2*x) / y -> y^2/2 = x^2 + C1
    {
        const Expr rhs = P(c, "2*x / y");
        const OdeResult sol = dsolve1(c, rhs, x, y);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde1(c, sol.y, rhs, x, y));
    }

    // 3. Bernoulli (n = 2): y' = (1/x)*y + x*y^2
    {
        const Expr rhs = P(c, "(1/x)*y + x*y^2");
        const OdeResult sol = dsolve1(c, rhs, x, y);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde1(c, sol.y, rhs, x, y));
    }
}

TEST(DsolveTest, FirstOrderIVP)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");

    // 1. y' = -2*y + 6, y(0) = 5 -> y(x) = 3 + 2*exp(-2*x)
    {
        const Expr rhs = P(c, "-2*y + 6");
        const OdeResult sol = dsolve1IVP(c, rhs, x, y, c.zero(), c.number(5));
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(sameExpr(c, sol.y, P(c, "3 + 2*exp(-2*x)")))
            << "got: " << c.toString(sol.y);
    }

    // 2. Separable IVP: y' = x * y^2, y(0) = 1 -> y(x) = 2 / (2 - x^2)
    {
        const Expr rhs = P(c, "x * y^2");
        const OdeResult sol = dsolve1IVP(c, rhs, x, y, c.zero(), c.one());
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(sameExpr(c, sol.y, P(c, "2 / (2 - x^2)")))
            << "got: " << c.toString(sol.y);
    }
}

TEST(DsolveTest, SecondOrderHomogeneousThreeRegimes)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // 1. Overdamped (distinct real roots r = 1, 2): y'' - 3*y' + 2*y = 0
    {
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.number(-3), c.number(2), c.zero(), x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.number(-3), c.number(2), c.zero(), x));
    }

    // 2. Critically damped (repeated root r = -2): y'' + 4*y' + 4*y = 0
    {
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.number(4), c.number(4), c.zero(), x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.number(4), c.number(4), c.zero(), x));
    }

    // 3. Undamped harmonic oscillator (r = +-2i): y'' + 4*y = 0
    {
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.zero(), c.number(4), c.zero(), x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.zero(), c.number(4), c.zero(), x));
    }

    // 4. Underdamped oscillator (r = -1 +- 2i): y'' + 2*y' + 5*y = 0
    {
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.number(2), c.number(5), c.zero(), x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.number(2), c.number(5), c.zero(), x));
    }
}

TEST(DsolveTest, SecondOrderForcedAndResonance)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // 1. Polynomial forcing: y'' - y = x^2
    {
        const Expr fx = P(c, "x^2");
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.zero(), c.number(-1), fx, x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.zero(), c.number(-1), fx, x));
    }

    // 2. Polynomial forcing with d = 0 resonance: y'' + y' = 2*x
    {
        const Expr fx = P(c, "2*x");
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.one(), c.zero(), fx, x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.one(), c.zero(), fx, x));
    }

    // 3. Non-resonant exponential forcing: y'' - 3*y' + 2*y = 4*exp(3*x)
    {
        const Expr fx = P(c, "4*exp(3*x)");
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.number(-3), c.number(2), fx, x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.number(-3), c.number(2), fx, x));
    }

    // 4. Simple exponential resonance (k = 1 is a simple root): y'' - 3*y' + 2*y = exp(x)
    {
        const Expr fx = P(c, "exp(x)");
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.number(-3), c.number(2), fx, x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.number(-3), c.number(2), fx, x));
    }

    // 5. Double exponential resonance (k = 1 is a double root): y'' - 2*y' + y = 6*exp(x)
    {
        const Expr fx = P(c, "6*exp(x)");
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.number(-2), c.one(), fx, x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.number(-2), c.one(), fx, x));
    }

    // 6. Non-resonant trigonometric forcing: y'' + 4*y = 3*sin(x)
    {
        const Expr fx = P(c, "3*sin(x)");
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.zero(), c.number(4), fx, x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.zero(), c.number(4), fx, x));
    }

    // 7. Pure trigonometric resonance: y'' + 4*y = 8*sin(2*x)
    {
        const Expr fx = P(c, "8*sin(2*x)");
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.zero(), c.number(4), fx, x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(checkOde2(c, sol.y, c.one(), c.zero(), c.number(4), fx, x));
    }
}

TEST(DsolveTest, SecondOrderIVP)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // 1. Harmonic oscillator IVP: y'' + y = 0, y(0) = 1, y'(0) = 2 -> cos(x) + 2*sin(x)
    {
        const OdeResult sol = dsolve2LinearIVP(
            c, c.one(), c.zero(), c.one(), c.zero(), x, c.zero(), c.one(), c.number(2));
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(sameExpr(c, sol.y, P(c, "cos(x) + 2*sin(x)")))
            << "got: " << c.toString(sol.y);
    }

    // 2. Critically damped IVP: y'' + 2*y' + y = 0, y(0) = 1, y'(0) = 0 -> (1 + x)*exp(-x)
    {
        const OdeResult sol = dsolve2LinearIVP(
            c, c.one(), c.number(2), c.one(), c.zero(), x, c.zero(), c.one(), c.zero());
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(sameExpr(c, sol.y, P(c, "(1 + x)*exp(-x)")))
            << "got: " << c.toString(sol.y);
    }

    // 3. Resonant forced IVP: y'' + y = cos(x), y(0) = 0, y'(0) = 0 -> 1/2*x*sin(x)
    {
        const Expr fx = P(c, "cos(x)");
        const OdeResult sol = dsolve2LinearIVP(
            c, c.one(), c.zero(), c.one(), fx, x, c.zero(), c.zero(), c.zero());
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(sameExpr(c, sol.y, P(c, "1/2*x*sin(x)")))
            << "got: " << c.toString(sol.y);
    }
}

// ============================================================================
// Layer 2: Property tests — randomized 1st- and 2nd-order linear ODEs
// ============================================================================

TEST(DsolveTest, RandomFirstAndSecondOrderLinearProperty)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    std::mt19937 rng(0xD5017E42u);
    std::uniform_int_distribution<int> coeffDist(-4, 4);

    for (int iter = 0; iter < 40; ++iter) {
        int a = coeffDist(rng);
        if (a == 0)
            a = 1;
        const int c0 = coeffDist(rng);
        const int c1 = coeffDist(rng);
        // 1st-order: y' = -a*y + c0 + c1*x
        const Expr rhs = c.add({c.mul({c.number(-a), y}),
                                c.number(c0), c.mul({c.number(c1), x})});
        const OdeResult sol1 = dsolve1(c, rhs, x, y);
        ASSERT_TRUE(sol1.proved()) << "iter " << iter << ": " << sol1.reason;
        EXPECT_TRUE(checkOde1(c, sol1.y, rhs, x, y));

        // 2nd-order: y'' + a*y' + b*y = c0 + c1*x
        const int b = coeffDist(rng);
        const Expr fx = c.add({c.number(c0), c.mul({c.number(c1), x})});
        const OdeResult sol2 =
            dsolve2Linear(c, c.one(), c.number(a), c.number(b), fx, x);
        ASSERT_TRUE(sol2.proved()) << "iter " << iter << ": " << sol2.reason;
        EXPECT_TRUE(checkOde2(c, sol2.y, c.one(), c.number(a), c.number(b), fx, x));
    }
}

// ============================================================================
// Layer 3: Boundary & edge cases
// ============================================================================

TEST(DsolveTest, BoundaryAndEdgeCases)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    const Expr C1 = c.symbol("C1");

    // 1. Null inputs return Unevaluated cleanly
    EXPECT_FALSE(dsolve1(c, Expr{}, x, y).proved());
    EXPECT_FALSE(dsolve2Linear(c, Expr{}, c.zero(), c.zero(), c.zero(), x).proved());

    // 2. Trivial ODE y' = 0 -> y = C1
    {
        const OdeResult sol = dsolve1(c, c.zero(), x, y);
        ASSERT_TRUE(sol.proved());
        EXPECT_EQ(sol.y, C1);
    }

    // 3. Free particle y'' = 0 -> y = C1 + C2*x
    {
        const OdeResult sol =
            dsolve2Linear(c, c.one(), c.zero(), c.zero(), c.zero(), x);
        ASSERT_TRUE(sol.proved()) << sol.reason;
        EXPECT_TRUE(sameExpr(c, sol.y, P(c, "C1 + C2*x")));
    }

    // 4. Non-elementary ODE y' = sin(x*y) returns honest Unevaluated
    {
        const OdeResult sol = dsolve1(c, P(c, "sin(x*y)"), x, y);
        EXPECT_FALSE(sol.proved());
        EXPECT_EQ(sol.status, OdeResult::Status::Unevaluated);
    }
}

} // namespace
} // namespace numkit::cas
