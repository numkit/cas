#include <numkit/cas/transform/fourier.hpp>

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

TEST(FourierTest, ForwardFourierFixedVectors)
{
    Ctx c;
    const Expr t = c.symbol("t");
    const Expr w = c.symbol("w");
    c.assume("a", AssumeDomain::Positive);
    c.assume("w0", AssumeDomain::Positive);

    struct Case {
        const char *f;
        const char *expected;
    };
    const Case cases[] = {
        // Generalized functions & sinusoids
        {"dirac(t)", "1"},
        {"dirac(t - 3)", "cos(3*w) - I*sin(3*w)"},
        {"dirac(t + 2)", "cos(2*w) + I*sin(2*w)"},
        {"1", "2*pi*dirac(w)"},
        {"5", "10*pi*dirac(w)"},
        {"cos(w0*t)", "pi*(dirac(w - w0) + dirac(w + w0))"},
        {"sin(w0*t)", "-I*pi*(dirac(w - w0) - dirac(w + w0))"},
        // Gaussian kernels & moments
        {"exp(-a*t^2)", "(pi/a)^(1/2)*exp(-w^2/(4*a))"},
        {"exp(-2*t^2)", "(pi/2)^(1/2)*exp(-w^2/8)"},
        {"t*exp(-a*t^2)", "-I*w/(2*a)*(pi/a)^(1/2)*exp(-w^2/(4*a))"},
        {"t^2*exp(-a*t^2)", "(2*a - w^2)/(4*a^2)*(pi/a)^(1/2)*exp(-w^2/(4*a))"},
        // Two-sided exponential & moments
        {"exp(-a*abs(t))", "2*a/(a^2 + w^2)"},
        {"abs(t)*exp(-a*abs(t))", "2*(a^2 - w^2)/(a^2 + w^2)^2"},
        {"sign(t)*exp(-a*abs(t))", "-2*I*w/(a^2 + w^2)"},
        {"t*exp(-a*abs(t))", "-4*I*a*w/(a^2 + w^2)^2"},
        // Causal / anti-causal exponentials
        {"exp(-a*t)*heaviside(t)", "(a - I*w)/(a^2 + w^2)"},
        {"t*exp(-a*t)*heaviside(t)", "(a^2 - w^2 - 2*I*a*w)/(a^2 + w^2)^2"},
        {"exp(a*t)*heaviside(-t)", "(a + I*w)/(a^2 + w^2)"},
        // Modulation
        {"exp(-a*abs(t))*cos(w0*t)",
         "a/(a^2 + (w - w0)^2) + a/(a^2 + (w + w0)^2)"},
        {"exp(-a*abs(t))*sin(w0*t)",
         "I*(a/(a^2 + (w + w0)^2) - a/(a^2 + (w - w0)^2))"},
        // Boxcar, sinc, and triangle pairs
        {"heaviside(a - abs(t))", "2*sin(a*w)/w"},
        {"sin(a*t)/t", "pi*heaviside(a - abs(w))"},
        {"(1 - cos(a*t))/t^2", "pi/2*(a - abs(w))*heaviside(a - abs(w))"},
        // Hyperbolic secant and cosecant kernels
        {"sech(a*t)", "pi/a*sech(pi*w/(2*a))"},
        {"sech(a*t)^2", "pi*w/a^2*csch(pi*w/(2*a))"},
        {"t*csch(a*t)", "pi^2/(2*a^2)*sech(pi*w/(2*a))^2"},
        // Rational functions via upper-half-plane contour integration
        {"1/(t^2 + 4)", "1/2*pi*exp(-2*abs(w))"},
        {"t/(t^2 + 1)^2", "-1/2*I*pi*w*exp(-abs(w))"},
        {"1/(t^2 + 1)^2", "1/2*pi*(1 + abs(w))*exp(-abs(w))"},
        {"1/((t^2 + 1)*(t^2 + 4))",
         "1/6*pi*(2*exp(-abs(w)) - exp(-2*abs(w)))"},
    };

    for (const auto &tc : cases) {
        const Expr f = parseExpr(c, tc.f);
        const Expr want = parseExpr(c, tc.expected);
        const FourierResult r = fourier(c, f, t, w);
        ASSERT_TRUE(r.proved()) << "f = " << tc.f << ": " << r.reason;
        EXPECT_TRUE(equivExpr(c, r.F, want))
            << "f = " << tc.f << "\n  got:  " << c.toString(r.F)
            << "\n  want: " << c.toString(want);
    }
}

TEST(FourierTest, InverseFourierFixedVectors)
{
    Ctx c;
    const Expr w = c.symbol("w");
    const Expr t = c.symbol("t");
    c.assume("a", AssumeDomain::Positive);
    c.assume("w0", AssumeDomain::Positive);

    struct Case {
        const char *F;
        const char *expected;
    };
    const Case cases[] = {
        {"1", "dirac(t)"},
        {"2*pi*dirac(w)", "1"},
        {"pi*(dirac(w - w0) + dirac(w + w0))", "cos(w0*t)"},
        {"-I*pi*(dirac(w - w0) - dirac(w + w0))", "sin(w0*t)"},
        {"(pi/a)^(1/2)*exp(-w^2/(4*a))", "exp(-a*t^2)"},
        {"2*a/(a^2 + w^2)", "exp(-a*abs(t))"},
        {"-2*I*w/(a^2 + w^2)", "sign(t)*exp(-a*abs(t))"},
        {"1/(a + I*w)", "exp(-a*t)*heaviside(t)"},
        {"1/(a + I*w)^2", "t*exp(-a*t)*heaviside(t)"},
        {"1/(a + I*w)^3", "1/2*t^2*exp(-a*t)*heaviside(t)"},
        {"(a - I*w)/(a^2 + w^2)", "exp(-a*t)*heaviside(t)"},
        {"2*sin(a*w)/w", "heaviside(a - abs(t))"},
        {"pi*heaviside(a - abs(w))", "sin(a*t)/t"},
        {"pi/a*sech(pi*w/(2*a))", "sech(a*t)"},
        {"1/2*pi*exp(-2*abs(w))", "1/(t^2 + 4)"},
    };

    for (const auto &tc : cases) {
        const Expr F = parseExpr(c, tc.F);
        const Expr want = parseExpr(c, tc.expected);
        const FourierResult r = ifourier(c, F, w, t);
        ASSERT_TRUE(r.proved()) << "F = " << tc.F << ": " << r.reason;
        EXPECT_TRUE(equivExpr(c, r.F, want))
            << "F = " << tc.F << "\n  got:  " << c.toString(r.F)
            << "\n  want: " << c.toString(want);
    }
}

// ============================================================================
// Layer 2: Property Tests (Linearity & Certified Round-Trip)
// ============================================================================

TEST(FourierTest, LinearityAndRoundTripProperty)
{
    Ctx c;
    const Expr t = c.symbol("t");
    const Expr w = c.symbol("w");

    const std::vector<Expr> basis = {
        parseExpr(c, "dirac(t)"),
        parseExpr(c, "exp(-t^2)"),
        parseExpr(c, "exp(-2*abs(t))"),
        parseExpr(c, "exp(-3*t)*heaviside(t)"),
        parseExpr(c, "1/(t^2 + 1)"),
        parseExpr(c, "sech(t)"),
    };

    std::mt19937_64 rng(0xF00E1EULL);
    std::uniform_int_distribution<std::size_t> idxDist(0, basis.size() - 1);
    std::uniform_int_distribution<int> coefDist(-4, 4);

    for (int iter = 0; iter < 40; ++iter) {
        const Expr f1 = basis[idxDist(rng)];
        const Expr f2 = basis[idxDist(rng)];
        int c1 = coefDist(rng);
        int c2 = coefDist(rng);
        if (c1 == 0)
            c1 = 1;
        if (c2 == 0)
            c2 = -2;

        const Expr comb =
            c.add({c.mul({c.number(c1), f1}), c.mul({c.number(c2), f2})});
        const FourierResult rComb = fourier(c, comb, t, w);
        const FourierResult r1 = fourier(c, f1, t, w);
        const FourierResult r2 = fourier(c, f2, t, w);
        ASSERT_TRUE(rComb.proved());
        ASSERT_TRUE(r1.proved());
        ASSERT_TRUE(r2.proved());

        const Expr linWant =
            c.add({c.mul({c.number(c1), r1.F}), c.mul({c.number(c2), r2.F})});
        EXPECT_TRUE(equivExpr(c, rComb.F, linWant));

        const FourierResult inv = ifourier(c, rComb.F, w, t);
        ASSERT_TRUE(inv.proved()) << "F = " << c.toString(rComb.F) << ": "
                                  << inv.reason;
        EXPECT_TRUE(equivExpr(c, inv.F, comb))
            << "round-trip failed for " << c.toString(comb)
            << "\n  got: " << c.toString(inv.F);
    }
}

// ============================================================================
// Layer 3: Boundary & Unsupported Cases
// ============================================================================

TEST(FourierTest, BoundaryAndInvalidInputs)
{
    Ctx c;
    const Expr t = c.symbol("t");
    const Expr w = c.symbol("w");

    // Zero function
    const FourierResult rZero = fourier(c, c.zero(), t, w);
    ASSERT_TRUE(rZero.proved());
    EXPECT_TRUE(c.isZero(rZero.F));

    const FourierResult iZero = ifourier(c, c.zero(), w, t);
    ASSERT_TRUE(iZero.proved());
    EXPECT_TRUE(c.isZero(iZero.F));

    // Null or non-symbol transform variable
    EXPECT_FALSE(fourier(c, Expr(), t, w).proved());
    EXPECT_FALSE(fourier(c, t, c.one(), w).proved());
    EXPECT_FALSE(ifourier(c, w, c.one(), t).proved());

    // Divergent exponential exp(t^2) is honestly Unevaluated
    const FourierResult rDiv = fourier(c, parseExpr(c, "exp(t^2)"), t, w);
    EXPECT_FALSE(rDiv.proved());
}

} // namespace
} // namespace numkit::cas
