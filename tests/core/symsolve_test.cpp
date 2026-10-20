#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/core/symsolve.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

namespace numkit::cas {
namespace {

bool containsRoot(Ctx &c, const std::vector<Expr> &roots, Expr target)
{
    for (const Expr &r : roots) {
        if (c.simplify(c.add({r, c.neg(target)})) == c.zero())
            return true;
    }
    return false;
}

bool containsPair(Ctx &c, const std::vector<std::pair<Expr, Expr>> &sols,
                  Expr wantX, Expr wantY)
{
    for (const auto &kv : sols) {
        if (c.simplify(c.add({kv.first, c.neg(wantX)})) == c.zero() &&
            c.simplify(c.add({kv.second, c.neg(wantY)})) == c.zero()) {
            return true;
        }
    }
    return false;
}

// ============================================================================
// Layer 1: Fixed Oracle Vectors
// ============================================================================

TEST(SymSolveTest, ParametricPolynomialEquations)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // Linear: a*x + b = 0 => x = -b/a
    {
        const auto roots = solveSymbolic(c, parseExpr(c, "a*x + b"), x);
        ASSERT_EQ(roots.size(), 1u);
        EXPECT_TRUE(containsRoot(c, roots, parseExpr(c, "-b/a")));
    }

    // General symbolic quadratic: a*x^2 + b*x + c = 0
    {
        const Expr q = parseExpr(c, "a*x^2 + b*x + c");
        const auto roots = solveSymbolic(c, q, x);
        ASSERT_EQ(roots.size(), 2u);
        EXPECT_TRUE(containsRoot(
            c, roots, parseExpr(c, "(-b - (b^2 - 4*a*c)^(1/2))/(2*a)")));
        EXPECT_TRUE(containsRoot(
            c, roots, parseExpr(c, "(-b + (b^2 - 4*a*c)^(1/2))/(2*a)")));
    }

    // Double symbolic root: x^2 - 2*a*x + a^2 = 0 => x = a
    {
        const auto roots =
            solveSymbolic(c, parseExpr(c, "x^2 - 2*a*x + a^2"), x);
        ASSERT_EQ(roots.size(), 1u);
        EXPECT_TRUE(containsRoot(c, roots, parseExpr(c, "a")));
    }

    // Difference of squares: x^2 - a^2 = 0 => x = -a, a
    {
        const auto roots = solveSymbolic(c, parseExpr(c, "x^2 - a^2"), x);
        ASSERT_EQ(roots.size(), 2u);
        EXPECT_TRUE(containsRoot(c, roots, parseExpr(c, "-a")));
        EXPECT_TRUE(containsRoot(c, roots, parseExpr(c, "a")));
    }

    // Biquadratic: x^4 - 5*x^2 + 4 = 0 => {-2, -1, 1, 2}
    {
        const auto roots =
            solveSymbolic(c, parseExpr(c, "x^4 - 5*x^2 + 4"), x);
        ASSERT_EQ(roots.size(), 4u);
        for (int r : {-2, -1, 1, 2})
            EXPECT_TRUE(containsRoot(c, roots, c.number(r)));
    }

    // Rational equation with removable pole: (x^2 - 1)/(x - 1) = 0 => {-1} only
    {
        const auto roots =
            solveSymbolic(c, parseExpr(c, "(x^2 - 1)/(x - 1)"), x);
        ASSERT_EQ(roots.size(), 1u);
        EXPECT_TRUE(containsRoot(c, roots, c.number(std::int64_t{-1})));
    }
}

TEST(SymSolveTest, UnivariateRationalAndRootOf)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // (x - 2)*(x^2 - 3) = 0 => {2, -3^(1/2), 3^(1/2)}
    {
        const auto roots =
            solveSymbolic(c, parseExpr(c, "x^3 - 2*x^2 - 3*x + 6"), x);
        ASSERT_EQ(roots.size(), 3u);
        EXPECT_TRUE(containsRoot(c, roots, c.number(std::int64_t{2})));
        EXPECT_TRUE(containsRoot(c, roots, parseExpr(c, "-3^(1/2)")));
        EXPECT_TRUE(containsRoot(c, roots, parseExpr(c, "3^(1/2)")));
    }

    // Irreducible cubic x^3 + x - 1 = 0 => 1 real RootOf atom
    {
        const auto roots = solveSymbolic(c, parseExpr(c, "x^3 + x - 1"), x);
        ASSERT_EQ(roots.size(), 1u);
        EXPECT_EQ(c.kind(roots[0]), NodeKind::RootOf);
        double val = 0.0;
        ASSERT_TRUE(c.evalDouble(roots[0], {}, val));
        EXPECT_NEAR(val * val * val + val - 1.0, 0.0, 1e-14);
    }
}

TEST(SymSolveTest, InvertibleTranscendentalEquations)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // 2*exp(3*x - 1) - 5 = 0 => x = (1 + log(5/2))/3
    {
        const auto roots =
            solveSymbolic(c, parseExpr(c, "2*exp(3*x - 1) - 5"), x);
        ASSERT_EQ(roots.size(), 1u);
        EXPECT_TRUE(
            containsRoot(c, roots, parseExpr(c, "(1 + log(5/2))/3")));
    }

    // log(2*x + 1) - y = 0 => x = (exp(y) - 1)/2
    {
        const auto roots =
            solveSymbolic(c, parseExpr(c, "log(2*x + 1) - y"), x);
        ASSERT_EQ(roots.size(), 1u);
        EXPECT_TRUE(containsRoot(c, roots, parseExpr(c, "(exp(y) - 1)/2")));
    }

    // sin(a*x + b) - k = 0 => x = (asin(k) - b)/a
    {
        const auto roots =
            solveSymbolic(c, parseExpr(c, "sin(a*x + b) - k"), x);
        ASSERT_EQ(roots.size(), 1u);
        EXPECT_TRUE(containsRoot(c, roots, parseExpr(c, "(asin(k) - b)/a")));
    }

    // sqrt(3*x + 1) - 4 = 0 => x = 5
    {
        const auto roots =
            solveSymbolic(c, parseExpr(c, "sqrt(3*x + 1) - 4"), x);
        ASSERT_EQ(roots.size(), 1u);
        EXPECT_TRUE(containsRoot(c, roots, c.number(std::int64_t{5})));
    }
}

TEST(SymSolveTest, NonlinearSystemsSylvesterResultant)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");

    // Circle + line: x^2 + y^2 - 25 = 0, x - y - 1 = 0 => (-3, -4), (4, 3)
    {
        const auto sols = solveSystem2(c, parseExpr(c, "x^2 + y^2 - 25"),
                                       parseExpr(c, "x - y - 1"), x, y);
        ASSERT_EQ(sols.size(), 2u);
        EXPECT_TRUE(containsPair(c, sols, c.number(-3), c.number(-4)));
        EXPECT_TRUE(containsPair(c, sols, c.number(4), c.number(3)));
    }

    // Parabola + line: y - x^2 = 0, y - x - 2 = 0 => (-1, 1), (2, 4)
    {
        const auto sols = solveSystem2(c, parseExpr(c, "y - x^2"),
                                       parseExpr(c, "y - x - 2"), x, y);
        ASSERT_EQ(sols.size(), 2u);
        EXPECT_TRUE(containsPair(c, sols, c.number(-1), c.number(1)));
        EXPECT_TRUE(containsPair(c, sols, c.number(2), c.number(4)));
    }

    // Hyperbola + circle: x*y - 6 = 0, x^2 + y^2 - 13 = 0
    // => (-3, -2), (-2, -3), (2, 3), (3, 2)
    {
        const auto sols = solveSystem2(c, parseExpr(c, "x*y - 6"),
                                       parseExpr(c, "x^2 + y^2 - 13"), x, y);
        ASSERT_EQ(sols.size(), 4u);
        EXPECT_TRUE(containsPair(c, sols, c.number(-3), c.number(-2)));
        EXPECT_TRUE(containsPair(c, sols, c.number(-2), c.number(-3)));
        EXPECT_TRUE(containsPair(c, sols, c.number(2), c.number(3)));
        EXPECT_TRUE(containsPair(c, sols, c.number(3), c.number(2)));
    }

    // Symbolic parametric linear system: x + y - 2*a = 0, x - y - 2*b = 0 => (a+b, a-b)
    {
        const auto sols = solveSystem2(c, parseExpr(c, "x + y - 2*a"),
                                       parseExpr(c, "x - y - 2*b"), x, y);
        ASSERT_EQ(sols.size(), 1u);
        EXPECT_TRUE(containsPair(c, sols, parseExpr(c, "a + b"),
                                 parseExpr(c, "a - b")));
    }
}

// ============================================================================
// Layer 2: Property Tests
// ============================================================================

TEST(SymSolveTest, PropertyQuadraticAndSystemResidualsVanish)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    std::mt19937 rng(0x5017E041u);
    std::uniform_int_distribution<int> rDist(-6, 6);

    // 1. Random quadratics with rational or quadratic-irrational roots
    for (int iter = 0; iter < 100; ++iter) {
        const int p = rDist(rng);
        const int q = std::abs(rDist(rng)) + 1; // (x - p)^2 - q = 0
        const Expr eqn = c.expand(c.add(
            {c.pow(c.add({x, c.number(-p)}), c.number(2)), c.number(-q)}));
        const auto roots = solveSymbolic(c, eqn, x);
        ASSERT_EQ(roots.size(), 2u);
        for (const Expr &r : roots) {
            const Expr res = c.simplify(c.subs(eqn, x, r));
            EXPECT_EQ(res, c.zero())
                << "iter " << iter << ": eqn=" << c.toString(eqn)
                << ", root=" << c.toString(r) << ", res=" << c.toString(res);
        }
    }

    // 2. Random parabola-line systems with planted intersection (x0, y0)
    for (int iter = 0; iter < 40; ++iter) {
        const int x0 = rDist(rng);
        const int y0 = rDist(rng);
        const int m = rDist(rng);
        // eq1: y - y0 - (x - x0)^2 = 0
        // eq2: y - y0 - m*(x - x0) = 0
        const Expr dx = c.add({x, c.number(-x0)});
        const Expr dy = c.add({y, c.number(-y0)});
        const Expr eq1 = c.expand(c.add({dy, c.neg(c.pow(dx, c.number(2)))}));
        const Expr eq2 = c.expand(c.add({dy, c.neg(c.mul({c.number(m), dx}))}));

        const auto sols = solveSystem2(c, eq1, eq2, x, y);
        EXPECT_TRUE(containsPair(c, sols, c.number(x0), c.number(y0)));
        for (const auto &kv : sols) {
            EXPECT_EQ(c.simplify(c.subs(c.subs(eq1, x, kv.first), y, kv.second)),
                      c.zero());
            EXPECT_EQ(c.simplify(c.subs(c.subs(eq2, x, kv.first), y, kv.second)),
                      c.zero());
        }
    }
}

// ============================================================================
// Layer 3: Boundary Tests
// ============================================================================

TEST(SymSolveTest, BoundaryCases)
{
    Ctx c;
    const Expr x = c.symbol("x");

    // Constant non-zero has no solutions
    EXPECT_TRUE(solveSymbolic(c, c.number(5), x).empty());

    // Positive-definite quadratic x^2 + 4 = 0 has no real roots
    EXPECT_TRUE(solveSymbolic(c, parseExpr(c, "x^2 + 4"), x).empty());

    // Pure pole 1/(x - 2) = 0 has no solutions
    EXPECT_TRUE(solveSymbolic(c, parseExpr(c, "1/(x - 2)"), x).empty());

    // Budget exhaustion
    Budget exhausted(0);
    EXPECT_TRUE(solveSymbolic(c, parseExpr(c, "x - 1"), x, &exhausted).empty());
    EXPECT_EQ(exhausted.status(), BudgetStatus::StepExhausted);
}

} // namespace
} // namespace numkit::cas
