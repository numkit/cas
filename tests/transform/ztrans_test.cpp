#include <numkit/cas/transform/ztrans.hpp>

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

TEST(ZTransTest, ForwardZTransFixedVectors)
{
    Ctx c;
    const Expr n = c.symbol("n");
    const Expr z = c.symbol("z");

    struct Case {
        const char *f;
        const char *expected;
    };
    const Case cases[] = {
        {"1", "z/(z - 1)"},
        {"5", "5*z/(z - 1)"},
        {"n", "z/(z - 1)^2"},
        {"n^2", "z*(z + 1)/(z - 1)^3"},
        {"n^3", "z*(z^2 + 4*z + 1)/(z - 1)^4"},
        {"a^n", "z/(z - a)"},
        {"2^n", "z/(z - 2)"},
        {"(-1)^n", "z/(z + 1)"},
        {"n*a^n", "a*z/(z - a)^2"},
        {"n*2^n", "2*z/(z - 2)^2"},
        {"n^2*3^n", "3*z*(z + 3)/(z - 3)^3"},
        {"1/2*n*(n - 1)*2^(n - 2)", "z/(z - 2)^3"},
        {"exp(a*n)", "z/(z - exp(a))"},
        {"sin(w*n)", "z*sin(w)/(z^2 - 2*z*cos(w) + 1)"},
        {"cos(w*n)", "z*(z - cos(w))/(z^2 - 2*z*cos(w) + 1)"},
        {"r^n*sin(w*n)", "r*z*sin(w)/(z^2 - 2*r*z*cos(w) + r^2)"},
        {"r^n*cos(w*n)", "z*(z - r*cos(w))/(z^2 - 2*r*z*cos(w) + r^2)"},
        {"sinh(a*n)", "z*sinh(a)/(z^2 - 2*z*cosh(a) + 1)"},
        {"cosh(a*n)", "z*(z - cosh(a))/(z^2 - 2*z*cosh(a) + 1)"},
    };

    for (const auto &tc : cases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr want = parseExpr(c, tc.expected);
        const ZTransResult r = ztrans(c, f, n, z);
        ASSERT_TRUE(r.proved()) << "f = " << tc.f << ": " << r.reason;
        EXPECT_TRUE(equivExpr(c, r.F, want))
            << "f = " << tc.f << "\n  got:  " << c.toString(r.F)
            << "\n  want: " << c.toString(want);
    }
}

TEST(ZTransTest, InverseZTransFixedVectors)
{
    Ctx c;
    const Expr z = c.symbol("z");
    const Expr n = c.symbol("n");

    struct Case {
        const char *F;
        const char *expected;
    };
    const Case cases[] = {
        {"z/(z - 1)", "1"},
        {"z/(z - 3)", "3^n"},
        {"z/(z + 2)", "(-2)^n"},
        {"z/(z - a)", "a^n"},
        {"z/(z - 1)^2", "n"},
        {"2*z/(z - 2)^2", "n*2^n"},
        {"z/(z - 2)^3", "1/2*n*(n - 1)*2^(n - 2)"},
        {"z/((z - 1)*(z - 2))", "2^n - 1"},
        {"z^2/((z - 1)*(z - 2))", "2*2^n - 1"},
        {"z/((z - 1)*(z - 2)^2)", "1 - 2^n + n*2^(n - 1)"},
        // Oscillatory poles z^2 + 1 = 0 => cos/sin(pi/2 * n)
        {"z^2/(z^2 + 1)", "cos(1/2*pi*n)"},
        {"z/(z^2 + 1)", "sin(1/2*pi*n)"},
        // Damped oscillatory poles (z - 1)^2 + 1 = z^2 - 2*z + 2
        // r = sqrt(2), cos(theta) = 1/sqrt(2) => theta = pi/4
        {"z*(z - 1)/(z^2 - 2*z + 2)", "2^(1/2*n)*cos(1/4*pi*n)"},
        {"z/(z^2 - 2*z + 2)", "2^(1/2*n)*sin(1/4*pi*n)"},
        // Irreducible quadratic with real algebraic roots: Fibonacci F(z) = z/(z^2 - z - 1)
        {"z/(z^2 - z - 1)",
         "5^(-1/2)*((1/2 + 1/2*5^(1/2))^n - (1/2 - 1/2*5^(1/2))^n)"},
        // Pole at z = 0 plus pole at z = 1: 1/(z - 1) = -1 + z/(z - 1) -> 1 - kroneckerDelta(n)
        {"1/(z - 1)", "1 - kroneckerDelta(n)"},
    };

    for (const auto &tc : cases) {
        const Expr F = parseExpr(c, tc.F);
        const Expr want = parseExpr(c, tc.expected);
        const ZTransResult r = iztrans(c, F, z, n);
        ASSERT_TRUE(r.proved()) << "F = " << tc.F << ": " << r.reason;
        // Forward Z-transform of r.F is already certified equal to F(z).
        // Also check numerical agreement at n = 0, 1, 2, 3, 4, 5 for non-parametric cases.
        if (std::string(tc.F).find('a') == std::string::npos &&
            std::string(tc.expected).find("kroneckerDelta") == std::string::npos) {
            for (int k = 0; k <= 5; ++k) {
                const Expr kExpr = c.number(k);
                const Expr gotK = c.subs(r.F, n, kExpr);
                const Expr wantK = c.subs(want, n, kExpr);
                EXPECT_TRUE(equivExpr(c, gotK, wantK))
                    << "F = " << tc.F << " at n = " << k
                    << "\n  got:  " << c.toString(gotK)
                    << "\n  want: " << c.toString(wantK);
            }
        } else {
            EXPECT_TRUE(equivExpr(c, r.F, want))
                << "F = " << tc.F << "\n  got:  " << c.toString(r.F)
                << "\n  want: " << c.toString(want);
        }
    }
}

TEST(ZTransTest, RsolveFixedVectors)
{
    Ctx c;
    const Expr n = c.symbol("n");

    // 1. First-order geometric: -3*y(n) + y(n+1) = 0, y(0) = 5 => 5 * 3^n
    {
        const std::vector<Expr> coeffs = {c.number(-3), c.one()};
        const RsolveResult gen = rsolve(c, coeffs, c.zero(), n);
        ASSERT_TRUE(gen.proved()) << gen.reason;

        const RsolveResult ivp = rsolveIVP(c, coeffs, c.zero(), n, {c.number(5)});
        ASSERT_TRUE(ivp.proved()) << ivp.reason;
        EXPECT_TRUE(equivExpr(c, ivp.y, parseExpr(c, "5*3^n")))
            << "got: " << c.toString(ivp.y);
    }

    // 2. First-order nonhomogeneous: -2*y(n) + y(n+1) = 1, y(0) = 0 => 2^n - 1
    {
        const std::vector<Expr> coeffs = {c.number(-2), c.one()};
        const RsolveResult ivp = rsolveIVP(c, coeffs, c.one(), n, {c.zero()});
        ASSERT_TRUE(ivp.proved()) << ivp.reason;
        EXPECT_TRUE(equivExpr(c, ivp.y, parseExpr(c, "2^n - 1")))
            << "got: " << c.toString(ivp.y);
    }

    // 3. Second-order distinct integer roots: 6*y(n) - 5*y(n+1) + y(n+2) = 0,
    //    y(0) = 1, y(1) = 4 => 2*3^n - 2^n
    {
        const std::vector<Expr> coeffs = {c.number(6), c.number(-5), c.one()};
        const RsolveResult gen = rsolve(c, coeffs, c.zero(), n);
        ASSERT_TRUE(gen.proved()) << gen.reason;

        const RsolveResult ivp =
            rsolveIVP(c, coeffs, c.zero(), n, {c.one(), c.number(4)});
        ASSERT_TRUE(ivp.proved()) << ivp.reason;
        EXPECT_TRUE(equivExpr(c, ivp.y, parseExpr(c, "2*3^n - 2^n")))
            << "got: " << c.toString(ivp.y);
    }

    // 4. Second-order repeated root: 4*y(n) - 4*y(n+1) + y(n+2) = 0,
    //    y(0) = 1, y(1) = 6 => (1 + 2*n)*2^n
    {
        const std::vector<Expr> coeffs = {c.number(4), c.number(-4), c.one()};
        const RsolveResult gen = rsolve(c, coeffs, c.zero(), n);
        ASSERT_TRUE(gen.proved()) << gen.reason;

        const RsolveResult ivp =
            rsolveIVP(c, coeffs, c.zero(), n, {c.one(), c.number(6)});
        ASSERT_TRUE(ivp.proved()) << ivp.reason;
        for (int k = 0; k <= 5; ++k) {
            const Expr gotK = c.subs(ivp.y, n, c.number(k));
            const Expr wantK =
                c.subs(parseExpr(c, "(1 + 2*n)*2^n"), n, c.number(k));
            EXPECT_TRUE(equivExpr(c, gotK, wantK)) << "at n = " << k;
        }
    }

    // 5. Fibonacci recurrence (Binet's formula):
    //    -y(n) - y(n+1) + y(n+2) = 0, y(0) = 0, y(1) = 1
    {
        const std::vector<Expr> coeffs = {c.number(-1), c.number(-1), c.one()};
        const RsolveResult gen = rsolve(c, coeffs, c.zero(), n);
        ASSERT_TRUE(gen.proved()) << gen.reason;

        const RsolveResult ivp =
            rsolveIVP(c, coeffs, c.zero(), n, {c.zero(), c.one()});
        ASSERT_TRUE(ivp.proved()) << ivp.reason;
        const int fib[] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34};
        for (int k = 0; k < 10; ++k) {
            const Expr gotK = c.subs(ivp.y, n, c.number(k));
            EXPECT_TRUE(equivExpr(c, gotK, c.number(fib[k])))
                << "k = " << k << ", got: " << c.toString(gotK);
        }
    }

    // 6. Resonance nonhomogeneous: -2*y(n) + y(n+1) = 2^n, y(0) = 0 => n * 2^(n-1)
    {
        const std::vector<Expr> coeffs = {c.number(-2), c.one()};
        const RsolveResult ivp =
            rsolveIVP(c, coeffs, parseExpr(c, "2^n"), n, {c.zero()});
        ASSERT_TRUE(ivp.proved()) << ivp.reason;
        for (int k = 0; k <= 6; ++k) {
            const Expr gotK = c.subs(ivp.y, n, c.number(k));
            const Expr wantK =
                c.subs(parseExpr(c, "n*2^(n - 1)"), n, c.number(k));
            EXPECT_TRUE(equivExpr(c, gotK, wantK)) << "at n = " << k;
        }
    }

    // 7. Third-order recurrence: -6*y(n) + 11*y(n+1) - 6*y(n+2) + y(n+3) = 0
    //    Roots: 1, 2, 3. With y(0)=3, y(1)=6, y(2)=14 => 1 + 2^n + 3^n
    {
        const std::vector<Expr> coeffs = {c.number(-6), c.number(11),
                                          c.number(-6), c.one()};
        const RsolveResult gen = rsolve(c, coeffs, c.zero(), n);
        ASSERT_TRUE(gen.proved()) << gen.reason;

        const RsolveResult ivp = rsolveIVP(
            c, coeffs, c.zero(), n, {c.number(3), c.number(6), c.number(14)});
        ASSERT_TRUE(ivp.proved()) << ivp.reason;
        EXPECT_TRUE(equivExpr(c, ivp.y, parseExpr(c, "1 + 2^n + 3^n")))
            << "got: " << c.toString(ivp.y);
    }
}

// ============================================================================
// Layer 2: Property Tests (Round-Trip & Recurrence Verification)
// ============================================================================

TEST(ZTransTest, RoundTripProperty)
{
    Ctx c;
    const Expr n = c.symbol("n");
    const Expr z = c.symbol("z");

    std::mt19937_64 rng(0x5A5452414E53ULL);
    std::uniform_int_distribution<int> rootDist(-4, 4);
    std::uniform_int_distribution<int> coeffDist(-5, 5);

    for (int iter = 0; iter < 150; ++iter) {
        int r1 = rootDist(rng);
        if (r1 == 0)
            r1 = 1;
        int r2 = rootDist(rng);
        if (r2 == 0)
            r2 = -1;
        int c1 = coeffDist(rng);
        if (c1 == 0)
            c1 = 1;
        int c2 = coeffDist(rng);

        // Build f(n) = c1 * r1^n + c2 * n * r2^n
        const Expr f = c.add({
            c.mul({c.number(c1), c.pow(c.number(r1), n)}),
            c.mul({c.number(c2), n, c.pow(c.number(r2), n)}),
        });

        const ZTransResult zf = ztrans(c, f, n, z);
        ASSERT_TRUE(zf.proved()) << "iter " << iter << ": " << zf.reason;

        const ZTransResult izf = iztrans(c, zf.F, z, n);
        ASSERT_TRUE(izf.proved()) << "iter " << iter << ": " << izf.reason;

        // Check numerical agreement at n = 0, 1, 2, 3
        for (int k = 0; k <= 3; ++k) {
            const Expr gotK = c.subs(izf.F, n, c.number(k));
            const Expr wantK = c.subs(f, n, c.number(k));
            EXPECT_TRUE(equivExpr(c, gotK, wantK))
                << "iter " << iter << " at n = " << k;
        }
    }
}

TEST(ZTransTest, RandomSecondOrderIVPProperty)
{
    Ctx c;
    const Expr n = c.symbol("n");

    std::mt19937_64 rng(0x52534F4C5645ULL);
    std::uniform_int_distribution<int> rootDist(-3, 3);
    std::uniform_int_distribution<int> initDist(-5, 5);

    for (int iter = 0; iter < 80; ++iter) {
        int r1 = rootDist(rng);
        if (r1 == 0)
            r1 = 1;
        int r2 = rootDist(rng);
        if (r2 == 0)
            r2 = 2;
        const int p1 = -(r1 + r2);
        const int p0 = r1 * r2;
        const int a0 = initDist(rng);
        const int a1 = initDist(rng);

        // Recurrence: p0*y(n) + p1*y(n+1) + y(n+2) = 0
        const std::vector<Expr> coeffs = {c.number(p0), c.number(p1), c.one()};

        const RsolveResult sol =
            rsolveIVP(c, coeffs, c.zero(), n, {c.number(a0), c.number(a1)});
        ASSERT_TRUE(sol.proved()) << "iter " << iter << ": " << sol.reason;

        // Verify initial values and recurrence values up to n = 5
        int seq[6];
        seq[0] = a0;
        seq[1] = a1;
        for (int k = 2; k < 6; ++k)
            seq[k] = -p1 * seq[k - 1] - p0 * seq[k - 2];

        for (int k = 0; k < 6; ++k) {
            const Expr gotK = c.subs(sol.y, n, c.number(k));
            EXPECT_TRUE(equivExpr(c, gotK, c.number(seq[k])))
                << "iter " << iter << " at n = " << k;
        }
    }
}

// ============================================================================
// Layer 3: Boundary & Honest Unevaluated
// ============================================================================

TEST(ZTransTest, HonestUnevaluatedBoundaries)
{
    Ctx c;
    const Expr n = c.symbol("n");
    const Expr z = c.symbol("z");

    // Non-causal / improper rational function in z (degree(N) > degree(D))
    {
        const ZTransResult r = iztrans(c, parseExpr(c, "z^2/(z - 1)"), z, n);
        EXPECT_FALSE(r.proved());
    }

    // Irreducible cubic denominator over Q[z] -> honest Unevaluated
    {
        const ZTransResult r =
            iztrans(c, parseExpr(c, "z/(z^3 - z - 1)"), z, n);
        EXPECT_FALSE(r.proved());
    }

    // Variable-coefficient recurrence -> honest Unevaluated
    {
        const RsolveResult r = rsolve(c, {n, c.one()}, c.zero(), n);
        EXPECT_FALSE(r.proved());
    }

    // Non-Z-transformable RHS -> honest Unevaluated
    {
        const RsolveResult r =
            rsolveIVP(c, {c.number(-1), c.one()}, parseExpr(c, "sin(n^2)"), n,
                      {c.zero()});
        EXPECT_FALSE(r.proved());
    }
}

} // namespace
} // namespace numkit::cas
