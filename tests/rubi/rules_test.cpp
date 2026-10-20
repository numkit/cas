// rubi/rules_test.cpp — three layers per AGENTS.md for the C2 step-2
// matcher over the committed 1.1.1.1 slice:
//   1. fixed vectors: rule selection for textbook shapes;
//   2. property: random (a+b*x)^m with the EXACT canonical arity
//      always selects rule 4 (index 3) and binds a, b, x, m;
//   3. boundary: shapes outside the slice decline (-1), arity
//      mismatches decline, no bindings leak on failure.
#include <numkit/cas/rubi/rules.hpp>
#include <numkit/cas/core/parser.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Ctx;
using numkit::cas::Expr;
using numkit::cas::NodeKind;
using numkit::cas::Rational;
using namespace numkit::cas::rubi;

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

TEST(RubiMatcher, FixedVectors)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // x^7: pattern x_^m_. -> bindings m = 7.
    {
        std::vector<Binding> b;
        const int r = matchFirst(t, c, c.pow(x, c.number(std::int64_t{7})), b);
        ASSERT_GE(r, 0);
        ASSERT_EQ(b.size(), 1u);
        EXPECT_EQ(b[0].name, "m");
        EXPECT_EQ(b[0].value, c.number(std::int64_t{7}));
    }
    // (2 + 3*x)^4: SPECIFICITY ordering (step 3b) prefers the
    // structural (a_.+b_.*x_)^m_ shape over the bare x_^m_. - the
    // Add base binds a, b, x individually.
    {
        const Expr e = c.pow(
            c.add({c.number(std::int64_t{2}),
                   c.mul({c.number(std::int64_t{3}), x})}),
            c.number(std::int64_t{4}));
        std::vector<Binding> b;
        const int r = matchFirst(t, c, e, b);
        ASSERT_GE(r, 0); // the (a+b x)^m rule leads among linear ^-shapes
        // x_ binds nothing (Symbol edge); a, b, m remain.
        ASSERT_EQ(b.size(), 3u);
        EXPECT_EQ(b[0].name, "a");
        EXPECT_EQ(b[1].name, "b");
        EXPECT_EQ(b[2].name, "m");
        EXPECT_EQ(b[0].value, c.number(std::int64_t{2}));
        EXPECT_EQ(b[2].value, c.number(std::int64_t{4}));
    }
}

TEST(RubiMatcher, BoundaryDeclines)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");
    std::vector<Binding> b;

    // 1/x canonicalizes to Pow(x,-1): the div-twin of 1/x_ (Pow[x_, -1])
    // beats x_^m_.
    const Expr oneOver = c.pow(x, c.number(std::int64_t{-1}));
    EXPECT_GE(matchFirst(t, c, oneOver, b), 0);
    // x_-literals bind NOTHING by design (Symbol edges) - only the
    // rule identity remains.
    EXPECT_EQ(b.size(), 0u);

    // besselj(x): no rule in the slice starts with an unknown special function.
    b.clear();
    EXPECT_EQ(matchFirst(t, c, c.func("besselj", x), b), -1);
    EXPECT_TRUE(b.empty()) << "no binding leaks on failure";

    // Bare x: the ^-chain requires two children; the wildcard-first
    // rules (x_ alone) exist only as the ^-chain's operand, not at
    // the top; decline.
    b.clear();
    EXPECT_EQ(matchFirst(t, c, x, b), -1);

    // Arity mismatch: a 5-factor Mul exceeds the maximum 4-factor
    // binomial product arity in 1.1.x and declines at the trie level.
    const Expr fiveMul = c.mul({c.number(std::int64_t{2}), x,
                                c.symbol("y"), c.symbol("z"),
                                c.symbol("w")});
    b.clear();
    EXPECT_EQ(matchFirst(t, c, fiveMul, b), -1);
}

TEST(RubiMatcher, Property)
{
    // Random (a+b*x)^(m/3) with a,b non-zero: the specificity order
    // must pick the STRUCTURAL (a+b x)^m rule and the certified
    // answer (a+bx)^(m+1)/(b(m+1)) differentiates back exactly.
    // (Rule indices are an implementation detail of the generator's
    // sort; the certificate is the durable invariant.)
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");
    std::uint64_t st = 0x2B1B4E5EEDULL;
    for (int iter = 0; iter < 3000; ++iter) {
        std::int64_t a = static_cast<std::int64_t>(nextU64(st) % 13) - 6;
        std::int64_t b = static_cast<std::int64_t>(nextU64(st) % 13) - 6;
        if (a == 0)
            a = 1; // a=0 collapses the two-term Add away; b=3 makes
        if (b == 0 || b == 3)
            b = 2; // the coefficient b/3 fold to 1*x = x; both leave
                   // the bare x_^m_. rule the legitimate winner
        std::int64_t m = static_cast<std::int64_t>(nextU64(st) % 9) - 4;
        // m/3 must stay fractional: an integer exponent folds
        // Number^m away entirely, leaving no Pow for the ^-rules.
        while (m % 3 == 0)
            m += 1;
        const Expr base = c.add(
            {c.number(Rational(BigInt(a), BigInt(3))),
             c.mul({c.number(Rational(BigInt(b), BigInt(3))), x})});
        const Expr e = c.pow(base, c.number(Rational(BigInt(m), BigInt(3))));
        std::vector<Binding> bs;
        const int r = matchFirst(t, c, e, bs);
        ASSERT_GE(r, 0) << "iter " << iter << " e=" << c.toString(e);
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull()) << "iter " << iter << " e=" << c.toString(e);
        ASSERT_EQ(c.diff(F, x), e) << "iter " << iter;
    }
}

} // namespace


// ── Step 3a: rule execution with certification ─────────────────

TEST(RubiApply, FirstCertifiedApplication)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // int x^7 dx = x^8/8 via x_^m_. with NeQ[m, -1] holding.
    const Expr F = rubiApply(t, c, c.pow(x, c.number(std::int64_t{7})), x);
    ASSERT_FALSE(F.isNull());
    EXPECT_EQ(c.toString(F), "1/8*x^8");
    EXPECT_EQ(c.diff(F, x), c.pow(x, c.number(std::int64_t{7})));
}

TEST(RubiApply, BoundaryAndGuards)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // 1/((1+x)*(1-x)): b*c + a*d == 0, so Rubi's primary rule 2 in
    // 1.1.1.2 cascades into Int[1/(1 - x^2), x] -> atanh(x).
    {
        const Expr F = rubiApply(
            t, c,
            c.mul({c.pow(c.add({c.one(), x}), c.number(std::int64_t{-1})),
                   c.pow(c.add({c.one(), c.neg(x)}),
                         c.number(std::int64_t{-1}))}),
            x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "atanh(x)");
    }

    // 1/((1+x)*(2-x)): b*c + a*d != 0, so rule 2 declines and rule 3
    // of 1.1.1.2 splits into two logarithms via recursive Int.
    {
        const Expr F = rubiApply(
            t, c,
            c.mul({c.pow(c.add({c.one(), x}), c.number(std::int64_t{-1})),
                   c.pow(c.add({c.number(std::int64_t{2}), c.neg(x)}),
                         c.number(std::int64_t{-1}))}),
            x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "-1/3*log(2 + -x) + 1/3*log(1 + x)");
    }

    // 1/(1+x^2): the QUADRATIC slice rule - atan(x), the textbook
    // arctangent integral, straight from Rubi (Rt[1,2] folds to 1).
    {
        const Expr F = rubiApply(
            t, c, c.pow(c.add({c.one(), c.pow(x, c.number(std::int64_t{2}))}),
                        c.number(std::int64_t{-1})), x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "atan(x)");
    }

    // 1/(2+3*x): the div-twin of the 1/(a+b x) rule fires, the
    // replacement Log[RemoveContent[...]]/b executes with content 1.
    {
        const Expr F = rubiApply(
            t, c, c.pow(c.add({c.number(std::int64_t{2}),
                               c.mul({c.number(std::int64_t{3}), x})}),
                        c.number(std::int64_t{-1})), x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/3*log(2 + 3*x)");
    }
    // 1/(2+4*x): RemoveContent STRIPS the content 2 - the answer
    // log(1+2x)/4 differentiates to (1/2)(1+2x)^-1, equal to
    // 1/(2+4x) only in Q(x): the POLYNOMIAL-grade gate.
    {
        const Expr F = rubiApply(
            t, c, c.pow(c.add({c.number(std::int64_t{2}),
                               c.mul({c.number(std::int64_t{4}), x})}),
                        c.number(std::int64_t{-1})), x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/4*log(1 + 2*x)");
    }
    // sqrt(2+3*x): fractional power - outside Q(x); the STRUCTURAL
    // fallback of the gate certifies (2/9)(2+3x)^(3/2).
    {
        const Expr e = c.pow(
            c.add({c.number(std::int64_t{2}),
                   c.mul({c.number(std::int64_t{3}), x})}),
            c.number(Rational(BigInt(1), BigInt(2))));
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "2/9*(2 + 3*x)^(3/2)");
    }

    // (2 + x)^4: the coefficient b folded away (1*x = x); the
    // optional-product synthesis binds b := 1 and the (a+b x)^m
    // rule certifies (2+x)^5/5.
    {
        const Expr e = c.pow(
            c.add({c.number(std::int64_t{2}), x}),
            c.number(std::int64_t{4}));
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/5*(2 + x)^5");
        EXPECT_EQ(c.diff(F, x), e);
    }

    // x^(-1): the DIVISION-TWIN rewrite matches the 1/x_ rule
    // (canonical Pow[x,-1]) and Log[x] certifies - the textbook
    // integral of 1/x, straight from Rubi.
    {
        const Expr F =
            rubiApply(t, c, c.pow(x, c.number(std::int64_t{-1})), x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "log(x)");
        EXPECT_EQ(c.diff(F, x), c.pow(x, c.number(std::int64_t{-1})));
    }

    // besselj(x): nothing in the slice matches.
    EXPECT_TRUE(rubiApply(t, c, c.func("besselj", x), x).isNull());

    // (2+3*x)^4: SPECIFICITY (step 3b) picks the (a+b x)^m rule and
    // the certificate PASSES: (2+3x)^5/15 differentiates back to
    // (2+3x)^4 exactly.
    const Expr e = c.pow(
        c.add({c.number(std::int64_t{2}),
               c.mul({c.number(std::int64_t{3}), x})}),
        c.number(std::int64_t{4}));
    const Expr F = rubiApply(t, c, e, x);
    ASSERT_FALSE(F.isNull());
    EXPECT_EQ(c.toString(F), "1/15*(2 + 3*x)^5");
    EXPECT_EQ(c.diff(F, x), e);
}

TEST(RubiApply, PropertyIntegerPowers)
{
    // Random integer exponents m in [-6..8] \ {-1, 0}: x^m -> x^(m+1)
    // /(m+1), certified. m = 0 canonicalizes x^0 to 1 (no Pow) and
    // m = -1 is declined by the rule itself.
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");
    std::uint64_t st = 0x3A3A5EEDULL;
    for (int iter = 0; iter < 2000; ++iter) {
        std::int64_t m = static_cast<std::int64_t>(nextU64(st) % 15) - 6;
        // m = 0, 1 canonicalize the power away (x^0 = 1, x^1 = x);
        // m = -1 is declined by the rule's own NeQ.
        if (m >= -1 && m <= 1)
            m = 2;
        const Expr e = c.pow(x, c.number(m));
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull()) << "m=" << m;
        ASSERT_EQ(c.diff(F, x), e) << "m=" << m;
        // The certificate (the diff identity above) is the real
        // check; the printed-form check covers positive exponents
        // only (negative ones canonicalize signs differently).
        if (m + 1 > 1)
            EXPECT_EQ(c.toString(F),
                      "1/" + std::to_string(m + 1) + "*x^" +
                          std::to_string(m + 1))
                << "m=" << m;
    }
}

// ── Positive powers (a+b x²)^p: reduction cascade + 9.1 utilities ──

TEST(RubiApply, PositivePowersQuadratic)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // p = 1: the canonical DAG folds (a+b*x^2)^1 to the bare Add; the
    // IntSum mirror splits it into the 9.1 constant rule and the
    // factor pull-out onto x^m.
    {
        const Expr e = c.add({c.number(std::int64_t{2}),
                              c.mul({c.number(std::int64_t{1}),
                                     c.pow(x, c.number(std::int64_t{2}))})});
        const Expr e2 = c.add({c.number(std::int64_t{2}), c.pow(x, c.number(std::int64_t{2}))});
        EXPECT_EQ(e, e2); // 1*x^2 folds - the two spellings agree
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/3*x^3 + 2*x");
        EXPECT_EQ(c.diff(F, x), e);
    }
    // p >= 2: the 1.1.2.1 reduction rule (GtQ[p,0] && IntegerQ[4*p])
    // cascades down to the p=1 bare Add; IntegerQ is the predicate
    // this cascade was blocked on before item 30.
    {
        const Expr e = c.pow(
            c.add({c.number(std::int64_t{6}),
                   c.mul({c.number(std::int64_t{4}),
                          c.pow(x, c.number(std::int64_t{2}))})}),
            c.number(std::int64_t{2}));
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        // the reduction form: x(6+4x²)²/5 + (24/5)(4/3x³ + 6x)
        EXPECT_EQ(c.toString(F),
                  "1/5*x*(6 + 4*x^2)^2 + 24/5*(4/3*x^3 + 6*x)");
    }
    // p = 4, b folded to 1: deepest cascade of the corpus slice. The
    // certificate inside rubiApply is polynomial-grade (dF equals the
    // integrand in Q(x), NOT structurally - the expanded derivative
    // does not refold to (1+x^2)^4), so the durable assertions are
    // the exact cascade form and its round-trip.
    {
        const Expr e = c.pow(
            c.add({c.one(), c.pow(x, c.number(std::int64_t{2}))}),
            c.number(std::int64_t{4}));
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F),
                  "1/9*x*(1 + x^2)^4 + 8/9*(1/7*x*(1 + x^2)^3 + 6/7*"
                  "(1/5*x*(1 + x^2)^2 + 4/5*(x + 1/3*x^3)))");
    }
}

TEST(RubiApply, LinearityFallbacks)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // Rubi 9.1 constant rule: Int[5, x] = 5*x - no table rule can
    // match a Number; the utility mirror carries it.
    {
        const Expr F = rubiApply(t, c, c.number(std::int64_t{5}), x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "5*x");
    }
    // Factor pull-out: Int[4*x^2, x] = 4*(x^3/3) - the canonical Mul
    // sorts its numeric factor first; the rest lands on x^m.
    {
        const Expr F = rubiApply(
            t, c, c.mul({c.number(std::int64_t{4}),
                         c.pow(x, c.number(std::int64_t{2}))}), x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "4/3*x^3");
    }
    // Negative factor: -x^2 -> -(x^3/3).
    {
        const Expr F = rubiApply(
            t, c, c.neg(c.pow(x, c.number(std::int64_t{2}))), x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "-1/3*x^3");
    }
    // IntSum honesty: ONE unintegrable term declines the whole sum -
    // 2 + besselj(x) stays Unevaluated rather than half-integrating.
    EXPECT_TRUE(rubiApply(
                    t, c,
                    c.add({c.number(std::int64_t{2}), c.func("besselj", x)}), x)
                    .isNull());
    // Bare linear monomials x and c*x (OneIdentity m=1 mirror):
    {
        const Expr F1 = rubiApply(t, c, x, x);
        ASSERT_FALSE(F1.isNull());
        EXPECT_EQ(c.toString(F1), "1/2*x^2");
        EXPECT_EQ(c.diff(F1, x), x);

        const Expr cx = c.mul({c.number(std::int64_t{4}), x});
        const Expr F2 = rubiApply(t, c, cx, x);
        ASSERT_FALSE(F2.isNull());
        EXPECT_EQ(c.toString(F2), "2*x^2");
        EXPECT_EQ(c.diff(F2, x), cx);
    }
    // Three-term Add (arity 3) including a linear term: every term integrates.
    {
        const Expr e = c.add(
            {c.number(std::int64_t{3}), c.pow(x, c.number(std::int64_t{2})),
             c.mul({c.number(std::int64_t{2}),
                    c.pow(x, c.number(std::int64_t{5}))})});
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/3*x^3 + 1/3*x^6 + 3*x");
        EXPECT_EQ(c.diff(F, x), e);
    }
}

TEST(RubiApply, PropertyPositivePowers)
{
    // Random (a+b*x^2)^p, p in [1..6], a,b in [-6..6]\\{0}: the
    // reduction cascade must always produce a CERTIFIED answer
    // (rubiApply already gates on the polynomial certificate) that
    // survives print/parse round-trip.
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");
    std::uint64_t st = 0x5EED30A11ULL;
    for (int iter = 0; iter < 2000; ++iter) {
        std::int64_t a = static_cast<std::int64_t>(nextU64(st) % 13) - 6;
        std::int64_t b = static_cast<std::int64_t>(nextU64(st) % 13) - 6;
        std::int64_t p = static_cast<std::int64_t>(nextU64(st) % 6) + 1;
        if (a == 0)
            a = 7; // a=0 collapses the Add; b=0 collapses the Mul -
        if (b == 0)  // both degeneracies are OTHER (still passing)
            b = 5;  // shapes: keep the two-term binomial here.
        const Expr e = c.pow(
            c.add({c.number(a),
                   c.mul({c.number(b), c.pow(x, c.number(std::int64_t{2}))})}),
            c.number(p));
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull()) << "a=" << a << " b=" << b << " p=" << p;
        // round-trip: the printed form parses back to the same DAG.
        const Expr back = numkit::cas::parseExpr(c, c.toString(F));
        ASSERT_FALSE(back.isNull()) << c.toString(F);
        ASSERT_EQ(back, F) << c.toString(F);
    }
}

// ── Stage R1a: canonical pattern rewrites, non-linear bindings, ────
// ── inverse trig/hyperbolic heads, and radical quotient gate    ────

TEST(RubiMatcher, NonlinearPatternRequiresEqualBindings)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // Equal exponents m == 2: matches the non-linear pattern
    // (a_ + b_.*x_)^m_ * (c_ + d_.*x_)^m_ first (bound wildcard "m"
    // beats fresh wildcard "n"), with a single binding for "m".
    {
        const Expr e = c.mul({
            c.pow(c.add({c.one(), x}), c.number(std::int64_t{2})),
            c.pow(c.add({c.one(), c.neg(x)}), c.number(std::int64_t{2})),
        });
        std::vector<Binding> b;
        const int r = matchFirst(t, c, e, b);
        ASSERT_GE(r, 0);
        int mCount = 0, nCount = 0;
        for (const Binding &bi : b) {
            if (bi.name == "m") ++mCount;
            if (bi.name == "n") ++nCount;
        }
        EXPECT_EQ(mCount, 1);
        EXPECT_EQ(nCount, 0);
    }

    // Distinct exponents 2 != 3: must NOT match the non-linear m_..m_
    // leaf; falls through to (a+b*x)^m_ * (c+d*x)^n_ and binds m=2, n=3.
    {
        const Expr e = c.mul({
            c.pow(c.add({c.one(), x}), c.number(std::int64_t{2})),
            c.pow(c.add({c.one(), c.neg(x)}), c.number(std::int64_t{3})),
        });
        std::vector<Binding> b;
        const int r = matchFirst(t, c, e, b);
        ASSERT_GE(r, 0);
        int mCount = 0, nCount = 0;
        for (const Binding &bi : b) {
            if (bi.name == "m") {
                ++mCount;
                EXPECT_EQ(bi.value, c.number(std::int64_t{2}));
            }
            if (bi.name == "n") {
                ++nCount;
                EXPECT_EQ(bi.value, c.number(std::int64_t{3}));
            }
        }
        EXPECT_EQ(mCount, 1);
        EXPECT_EQ(nCount, 1);
    }
}

TEST(RubiApply, R1aInverseTrigAndHyperbolic)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // 1/(1 - x^2) -> atanh(x)
    {
        const Expr e = numkit::cas::parseExpr(c, "1/(1 - x^2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "atanh(x)");
    }
    // 1/(2 - 3*x^2) -> 2^(-1/2)*3^(-1/2)*atanh(x*2^(-1/2)*3^(1/2))
    {
        const Expr e = numkit::cas::parseExpr(c, "1/(2 - 3*x^2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F),
                  "2^(-1/2)*3^(-1/2)*atanh(x*2^(-1/2)*3^(1/2))");
    }
    // 1/sqrt(1 + x^2) -> asinh(x) (pattern 1/Sqrt[a+b*x^2] canonicalized)
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x^2)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "asinh(x)");
    }
    // 1/sqrt(2 + 3*x^2) -> 3^(-1/2)*asinh(x*2^(-1/2)*3^(1/2))
    // Certified by Grade 1d (algebraic radical quotient Q^2 == 1 in Q(x)).
    {
        const Expr e = numkit::cas::parseExpr(c, "(2 + 3*x^2)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "3^(-1/2)*asinh(x*2^(-1/2)*3^(1/2))");
    }
    // 1/sqrt(1 - x^2) -> asin(x)
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 - x^2)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "asin(x)");
    }
    // 1/sqrt(2 - 9*x^2) -> 1/3*asin(3*x*2^(-1/2))
    {
        const Expr e = numkit::cas::parseExpr(c, "(2 - 9*x^2)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/3*asin(3*x*2^(-1/2))");
    }
    // 1/(sqrt(2 + 3*x)*sqrt(-2 + 3*x)) -> 1/3*acosh(3/2*x)
    {
        const Expr e =
            numkit::cas::parseExpr(c, "(2 + 3*x)^(-1/2)*(-2 + 3*x)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/3*acosh(3/2*x)");
    }
}

TEST(RubiApply, R1aFractionalAndNegativePowers)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // 1/(2 + 3*x^2)^(3/2) -> 1/2*x*(2 + 3*x^2)^(-1/2)
    {
        const Expr e = numkit::cas::parseExpr(c, "(2 + 3*x^2)^(-3/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/2*x*(2 + 3*x^2)^(-1/2)");
    }
    // (2 + 3*x^2)^(-5/2): ILtQ[p + 3/2, 0] reduction to (-3/2)
    {
        const Expr e = numkit::cas::parseExpr(c, "(2 + 3*x^2)^(-5/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F),
                  "1/6*x*(2 + 3*x^2)^(-3/2) + 1/6*x*(2 + 3*x^2)^(-1/2)");
    }
    // 1/(1 + x^2)^2: negative integer power reduction -> 1/2*x*(1+x^2)^-1 + 1/2*atan(x)
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x^2)^-2");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "1/2*x*(1 + x^2)^-1 + 1/2*atan(x)");
    }
    // Elliptic-only fractional power (1 + x^2)^(1/4): EllipticE rules
    // decline honestly and self-recursion / bounded-depth guards prevent
    // normalization rules (a=1 -> Int[(1+b*x^2/a)^(1/4), x]) from looping.
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x^2)^(1/4)");
        EXPECT_TRUE(rubiApply(t, c, e, x).isNull());
    }
    // (3*x^2)^(3/2): IntPart / FracPart rule in 1.1.2.1
    {
        const Expr e = c.pow(
            c.mul({c.number(std::int64_t{3}), c.pow(x, c.number(std::int64_t{2}))}),
            c.number(Rational(std::int64_t{3}, BigInt(2))));
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // Two-factor reduction with binary Mul commutativity and IntLinearQ:
    // (1 + x)^-2 * (2 + x)^-2 -> rational + logs
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x)^-2*(2 + x)^-2");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // Equal-exponent two-factor rule (1 + x)^2 * (1 - x)^2 -> Int[(1 - x^2)^2, x]
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x)^2*(1 - x)^2");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
}

TEST(RubiApply, PropertyR1aShapes)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");
    std::uint64_t st = 0x71A2026ULL;
    for (int iter = 0; iter < 1000; ++iter) {
        const std::int64_t a = 1 + static_cast<std::int64_t>(nextU64(st) % 6);
        const std::int64_t bMag = 1 + static_cast<std::int64_t>(nextU64(st) % 6);
        const std::int64_t b = (nextU64(st) % 2 == 0) ? bMag : -bMag;
        const int shape = static_cast<int>(nextU64(st) % 4);
        Expr e;
        if (shape == 0) {
            // 1/(a + b*x^2) with both positive and negative b (atan & atanh)
            e = c.pow(c.add({c.number(a),
                             c.mul({c.number(b), c.pow(x, c.number(std::int64_t{2}))})}),
                      c.number(std::int64_t{-1}));
        } else if (shape == 1) {
            // 1/sqrt(a + b*x^2) with a > 0 and both signs of b (asinh & asin)
            e = c.pow(c.add({c.number(a),
                             c.mul({c.number(b), c.pow(x, c.number(std::int64_t{2}))})}),
                      c.number(Rational(std::int64_t{-1}, BigInt(2))));
        } else if (shape == 2) {
            // (a + b*x^2)^(-3/2) and (-5/2)
            const std::int64_t num = (nextU64(st) % 2 == 0) ? -3 : -5;
            e = c.pow(c.add({c.number(a),
                             c.mul({c.number(b), c.pow(x, c.number(std::int64_t{2}))})}),
                      c.number(Rational(num, BigInt(2))));
        } else {
            // 1/(a + b*x^2)^2
            e = c.pow(c.add({c.number(a),
                             c.mul({c.number(b), c.pow(x, c.number(std::int64_t{2}))})}),
                      c.number(std::int64_t{-2}));
        }
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull())
            << "shape=" << shape << " a=" << a << " b=" << b
            << " e=" << c.toString(e);
        const Expr back = numkit::cas::parseExpr(c, c.toString(F));
        ASSERT_FALSE(back.isNull()) << c.toString(F);
        ASSERT_EQ(back, F);
    }
}

TEST(RubiApply, R1bSubstWithAndMultiFactor)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // 1.1.1.2 Reduction + Subst: 1/((1 + x)*(2 + x)^(1/2))
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x)^-1*(2 + x)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.1.2 Subst with Sqrt[a + b*x]: 1/(sqrt(1 + x)*sqrt(3 + x))
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x)^(-1/2)*(3 + x)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.1.2 Fractional power reduction + Subst: (1 + x)^(-3/2)*(3 + x)^(-1/2)
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x)^(-3/2)*(3 + x)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.1.3 Three-factor linear binomial product: 1/((1 + x)*(2 + x)*(3 + x))
    {
        const Expr e =
            numkit::cas::parseExpr(c, "(1 + x)^-1*(2 + x)^-1*(3 + x)^-1");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.1.3 Positive powers with ExpandIntegrand: (1 + x)^2*(2 + x)*(3 + x)
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x)^2*(2 + x)*(3 + x)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.1.4 Four-factor linear binomial product: 1/((1+x)*(2+x)*(3+x)*(4+x))
    {
        const Expr e = numkit::cas::parseExpr(
            c, "(1 + x)^-1*(2 + x)^-1*(3 + x)^-1*(4 + x)^-1");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
}

TEST(RubiApply, R2GeneralBinomialsAndExpandIntegrand)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    // 1.1.2.2 (c*x)^m*(a + b*x^2)^p: x^3*(2 + 3*x^2)^(1/2)
    {
        const Expr e = numkit::cas::parseExpr(c, "x^3*(2 + 3*x^2)^(1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.2.2 1/(x*sqrt(1 + x^2)) -> -atanh((1 + x^2)^(-1/2))
    {
        const Expr e = numkit::cas::parseExpr(c, "x^-1*(1 + x^2)^(-1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.2.3 (a + b*x^2)^p*(c + d*x^2)^q: 1/((1 + x^2)*(2 + x^2))
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x^2)^-1*(2 + x^2)^-1");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.2.7 (c + d*x)^n*(a + b*x^2)^p: (1 + 2*x)/(1 + x^2)
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + 2*x)*(1 + x^2)^-1");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.2.10 P(x)*(a + b*x^2)^p via ExpandIntegrand: (1 + x + x^2)/(2 + 3*x^2)
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 + x + x^2)*(2 + 3*x^2)^-1");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.3.1 1/(a - b*x^4) via With + Rt: 1/(1 - x^4)
    {
        const Expr e = numkit::cas::parseExpr(c, "(1 - x^4)^-1");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.3.2 x^2*sqrt(1 + x^3)
    {
        const Expr e = numkit::cas::parseExpr(c, "x^2*(1 + x^3)^(1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
    // 1.1.4.1 Improper binomial (a*x^j + b*x^n)^p: (x^2 + x^4)^(1/2)
    {
        const Expr e = numkit::cas::parseExpr(c, "(x^2 + x^4)^(1/2)");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
    }
}

TEST(RubiApply, PropertyR1bR2Shapes)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");
    std::uint64_t st = 0x52B2026ULL;
    for (int iter = 0; iter < 500; ++iter) {
        const std::int64_t a = 1 + static_cast<std::int64_t>(nextU64(st) % 5);
        const std::int64_t b = 1 + static_cast<std::int64_t>(nextU64(st) % 5);
        const std::int64_t d = a + 1 + static_cast<std::int64_t>(nextU64(st) % 4);
        const int shape = static_cast<int>(nextU64(st) % 5);
        Expr e;
        if (shape == 0) {
            // 1.1.2.2: x^m * (a + b*x^2)^(1/2), m in {1, 3}
            const std::int64_t m = (nextU64(st) % 2 == 0) ? 1 : 3;
            e = c.mul({c.pow(x, c.number(m)),
                       c.pow(c.add({c.number(a),
                                    c.mul({c.number(b),
                                           c.pow(x, c.number(std::int64_t{2}))})}),
                             c.number(Rational(std::int64_t{1}, BigInt(2))))});
        } else if (shape == 1) {
            // 1.1.2.3: 1/((a + x^2)*(d + x^2))
            e = c.mul({c.pow(c.add({c.number(a),
                                    c.pow(x, c.number(std::int64_t{2}))}),
                             c.number(std::int64_t{-1})),
                       c.pow(c.add({c.number(d),
                                    c.pow(x, c.number(std::int64_t{2}))}),
                             c.number(std::int64_t{-1}))});
        } else if (shape == 2) {
            // 1.1.1.3: 1/((a + x)*(d + x)*(d + b + x))
            e = c.mul({c.pow(c.add({c.number(a), x}), c.number(std::int64_t{-1})),
                       c.pow(c.add({c.number(d), x}), c.number(std::int64_t{-1})),
                       c.pow(c.add({c.number(d + b), x}),
                             c.number(std::int64_t{-1}))});
        } else if (shape == 3) {
            // 1.1.2.10: (a + b*x + d*x^2)/(a + b*x^2)
            const Expr poly = c.add(
                {c.number(a), c.mul({c.number(b), x}),
                 c.mul({c.number(d), c.pow(x, c.number(std::int64_t{2}))})});
            const Expr quad = c.add(
                {c.number(a),
                 c.mul({c.number(b), c.pow(x, c.number(std::int64_t{2}))})});
            e = c.mul({poly, c.pow(quad, c.number(std::int64_t{-1}))});
        } else {
            // 1.1.3.2: x^(n-1) * (a + b*x^n)^(-1/2), n in {3, 4}
            const std::int64_t n = (nextU64(st) % 2 == 0) ? 3 : 4;
            e = c.mul({c.pow(x, c.number(n - 1)),
                       c.pow(c.add({c.number(a),
                                    c.mul({c.number(b), c.pow(x, c.number(n))})}),
                             c.number(Rational(std::int64_t{-1}, BigInt(2))))});
        }
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull())
            << "shape=" << shape << " e=" << c.toString(e);
    }
}

TEST(RubiApply, R3Trinomials)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    const char *const kCases[] = {
        "(1 + x + x^2)^-1",
        "(2 + 3*x + x^2)^-1",
        "(1 + 2*x + x^2)^-1",
        "(1 + x + x^2)^-2",
        "(2 + 3*x + x^2)^-2",
        "(1 + x + x^2)^(-1/2)",
        "(1 + 3*x + x^2)^(-1/2)",
        "(1 + x + x^2)^(1/2)",
        "(1 + x + x^2)^(-3/2)",
        "(1 + x + x^2)^2",
        "(1 + 2*x)*(1 + x + x^2)^-1",
        "(1 + 2*x)*(1 + x + x^2)^(-1/2)",
        "(1 + 2*x)*(1 + x + x^2)^(1/2)",
        "(1 + 3*x^2 + 2*x^4)^-1",
        "(1 + 2*x^2 + x^4)^-1",
    };
    for (const char *s : kCases) {
        const Expr e = numkit::cas::parseExpr(c, s);
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull()) << "failed on R3 trinomial: " << s;
    }
}

TEST(RubiApply, R4ExponentialsAndLogs)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    const char *const kCases[] = {
        "exp(2*x)",
        "exp(1 + 3*x)",
        "x*exp(2*x)",
        "x^2*exp(3*x)",
        "(1 + 2*x)*exp(x)",
        "(1 + exp(x))^-1",
        "(2 + 3*exp(2*x))^-1",
        "(1 + exp(x))^-2",
        "exp(x)*(1 + exp(x))^-1",
        "exp(x)*(1 + exp(2*x))^-1",
        "exp(x)*(1 - exp(2*x))^(-1/2)",
        "exp(x)*(1 + exp(2*x))^(-1/2)",
        "log(x)",
        "log(2*x)",
        "log(x)^2",
        "log(x)^3",
        "x*log(x)",
        "x^3*log(x)",
        "x^2*log(x)^2",
        "x^-1*log(x)",
        "x^-1*log(x)^2",
        "x^-1*(1 + log(x))^-1",
        "x^-1*(1 + log(x))^(-1/2)",
    };
    for (const char *s : kCases) {
        const Expr e = numkit::cas::parseExpr(c, s);
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull()) << "failed on R4 exp/log: " << s;
    }
}

TEST(RubiApply, R5TrigInverseTrigHyperbolic)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");

    const char *const kCases[] = {
        // 4. Trig
        "sin(x)",
        "sin(1 + 2*x)",
        "cos(x)",
        "cos(3*x)",
        "sin(x)^2",
        "cos(x)^2",
        "sin(x)^3",
        "cos(x)^3",
        "sin(x)^4",
        "cos(x)^4",
        "sin(x)^-1",
        "cos(x)^-1",
        "sin(x)^-2",
        "cos(x)^-2",
        "tan(x)",
        "tan(2*x)",
        "tan(x)^2",
        "tan(x)^3",
        "cot(x)",
        "cot(x)^2",
        "sec(x)",
        "sec(x)^2",
        "sec(x)^3",
        "csc(x)",
        "csc(x)^2",
        "sin(x)*cos(x)",
        "sin(x)^2*cos(x)",
        "sin(x)*cos(x)^2",
        "cos(x)*(1 + sin(x))^-1",
        "sin(x)*(2 + cos(x))^-1",
        "(2 + sin(x))^-1",
        "(2 + cos(x))^-1",
        "x*sin(x)",
        "x*cos(x)",
        "x^2*sin(x)",
        "x^2*cos(x)",
        "exp(x)*sin(x)",
        "exp(2*x)*cos(3*x)",
        // 5. Inverse trig
        "asin(x)",
        "asin(2*x)",
        "x*asin(x)",
        "acos(x)",
        "x*acos(x)",
        "atan(x)",
        "atan(3*x)",
        "x*atan(x)",
        "x^2*atan(x)",
        "acot(x)",
        // 6. Hyperbolic
        "sinh(x)",
        "cosh(x)",
        "tanh(x)",
        "coth(x)",
        "sech(x)",
        "csch(x)",
        "sinh(x)^2",
        "cosh(x)^2",
        "sinh(x)^3",
        "cosh(x)^3",
        "tanh(x)^2",
        "sech(x)^2",
        "csch(x)^2",
        "cosh(x)*(1 + sinh(x))^-1",
        "sinh(x)*(1 + cosh(x))^-1",
        "x*sinh(x)",
        "x*cosh(x)",
        "exp(2*x)*sinh(x)",
        "exp(2*x)*cosh(x)",
        // 7. Inverse hyperbolic
        "asinh(x)",
        "x*asinh(x)",
        "acosh(x)",
        "x*acosh(x)",
        "atanh(x)",
        "x*atanh(x)",
    };
    for (const char *s : kCases) {
        const Expr e = numkit::cas::parseExpr(c, s);
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull()) << "failed on R5 trig/hyperbolic: " << s;
    }
}

TEST(RubiApply, PropertyR3R4R5Shapes)
{
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");
    std::uint64_t st = 0x402026ULL;
    for (int iter = 0; iter < 300; ++iter) {
        const std::int64_t a = 1 + static_cast<std::int64_t>(nextU64(st) % 4);
        const std::int64_t b = 1 + static_cast<std::int64_t>(nextU64(st) % 4);
        const int shape = static_cast<int>(nextU64(st) % 5);
        Expr e;
        if (shape == 0) {
            // R3: 1/(a + b*x + a*b*x^2) (positive 4ac - b^2 when 4a^2b > b^2)
            const Expr trinom = c.add(
                {c.number(a + b), c.mul({c.number(b), x}),
                 c.mul({c.number(a), c.pow(x, c.number(std::int64_t{2}))})});
            e = c.pow(trinom, c.number(std::int64_t{-1}));
        } else if (shape == 1) {
            // R4: x * exp(a + b*x)
            e = c.mul({x, c.func("exp", c.add({c.number(a),
                                               c.mul({c.number(b), x})}))});
        } else if (shape == 2) {
            // R4: x^a * log(b*x)
            e = c.mul({c.pow(x, c.number(a)),
                       c.func("log", c.mul({c.number(b), x}))});
        } else if (shape == 3) {
            // R5: sin(a + b*x)^3
            e = c.pow(c.func("sin", c.add({c.number(a),
                                           c.mul({c.number(b), x})})),
                      c.number(std::int64_t{3}));
        } else {
            // R5: x * cos(a + b*x)
            e = c.mul({x, c.func("cos", c.add({c.number(a),
                                               c.mul({c.number(b), x})}))});
        }
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull())
            << "shape=" << shape << " e=" << c.toString(e);
    }
}

TEST(RubiApply, AssumptionsSymbolicParameters)
{
    const RuleTables t = sliceTables();

    // When a > 0 and b > 0, PosQ[a/b] holds and Rt[a/b, 2] evaluates to
    // (a/b)^(1/2), giving the atan form for 1/(a + b*x^2).
    {
        Ctx c;
        const Expr x = c.symbol("x");
        c.assume("a", numkit::cas::AssumeDomain::Positive);
        c.assume("b", numkit::cas::AssumeDomain::Positive);
        const Expr e = numkit::cas::parseExpr(c, "(a + b*x^2)^-1");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_NE(c.toString(F).find("atan"), std::string::npos)
            << c.toString(F);
    }

    // When a > 0 and b < 0, NegQ[a/b] holds and Rt[-a/b, 2] evaluates to
    // (-a/b)^(1/2), giving the atanh form for 1/(a + b*x^2).
    {
        Ctx c;
        const Expr x = c.symbol("x");
        c.assume("a", numkit::cas::AssumeDomain::Positive);
        c.assume("b", numkit::cas::AssumeDomain::Negative);
        const Expr e = numkit::cas::parseExpr(c, "(a + b*x^2)^-1");
        const Expr F = rubiApply(t, c, e, x);
        ASSERT_FALSE(F.isNull());
        EXPECT_NE(c.toString(F).find("atanh"), std::string::npos)
            << c.toString(F);
    }
}




