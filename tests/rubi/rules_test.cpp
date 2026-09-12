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

    // x^7: pattern x_^m_. -> rule index 1, bindings x and m.
    {
        std::vector<Binding> b;
        const int r = matchFirst(t, c, c.pow(x, c.number(std::int64_t{7})), b);
        // specificity ordering: x_^m_. is the LEAST specific ^-rule
        // -> last index after the generator's sort (77 with both new
        // slices loaded). The x_ literal binds nothing (Symbol edge);
        // only m is bound.
        ASSERT_EQ(r, 77);
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
        ASSERT_EQ(r, 74); // the (a+b x)^m rule leads among ^-shapes
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

    // 1/x canonicalizes to x^-1 = Mul[x, Pow[x,-1]]... actually
    // Pow(x,-1): the /-patterns of rules 0 and 2 cannot match (the
    // DAG has no /); the ^-chain expects arity-2 shapes, x^-1 IS
    // Pow[x,-1] with pattern x_^m_. matching! It selects rule 1.
    const Expr oneOver = c.pow(x, c.number(std::int64_t{-1}));
    // the div-twin of 1/x_ (now Pow[ANY, -1]) beats x_^m_.
    EXPECT_EQ(matchFirst(t, c, oneOver, b), 76);
    // x_-literals bind NOTHING by design (Symbol edges) - only the
    // rule identity remains.
    EXPECT_EQ(b.size(), 0u);

    // sin(x): no rule in the slice starts with a Func head.
    b.clear();
    EXPECT_EQ(matchFirst(t, c, c.func("sin", x), b), -1);
    EXPECT_TRUE(b.empty()) << "no binding leaks on failure";

    // Bare x: the ^-chain requires two children; the wildcard-first
    // rules (x_ alone) exist only as the ^-chain's operand, not at
    // the top; decline.
    b.clear();
    EXPECT_EQ(matchFirst(t, c, x, b), -1);

    // Arity mismatch: x^(2+3) canonicalizes the exponent to a
    // Number (rule 1 still fine); build a 3-child Add to break the
    // exact-arity requirement through (a+b*x)^m's inner Add... our
    // canonical Add flattens, so craft Pow with an Add exponent of a
    // DIFFERENT pattern: (a+b*x)^(m+n) - exponent is an Add, not a
    // wildcard-only leaf under rule 3's m_ chain position... m_ is a
    // wildcard: it binds ANY subtree including Add - still rule 3.
    // The true decline: Pow with a THREE-operand Mul base where the
    // slice expects the two-term Add.
    const Expr three = c.pow(
        c.mul({c.number(std::int64_t{2}), x, c.symbol("y")}),
        c.number(std::int64_t{4}));
    b.clear();
    EXPECT_EQ(matchFirst(t, c, three, b), -1);
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
        ASSERT_EQ(r, 74) << "iter " << iter << " e=" << c.toString(e);
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

    // 1/((1+x)*(1-x)): the TWO-FACTOR slice - textbook partial
    // fractions through the RECURSIVE Int cascade (each inner
    // 1/(a+b x) lands on the log rule; the outer certificate
    // checks the assembled sum).
    {
        const Expr F = rubiApply(
            t, c,
            c.mul({c.pow(c.add({c.one(), x}), c.number(std::int64_t{-1})),
                   c.pow(c.add({c.one(), c.neg(x)}),
                         c.number(std::int64_t{-1}))}),
            x);
        ASSERT_FALSE(F.isNull());
        EXPECT_EQ(c.toString(F), "-1/2*log(1 + -x) + 1/2*log(1 + x)");
        // the POLYNOMIAL-grade certificate inside rubiApply already
        // verified dF == 1/((1+x)(1-x)) in Q(x) - no need (and no
        // way) to re-check structurally: the derivative prints as a
        // sum, the integrand as a product.
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

    // sin(x): nothing in the slice matches.
    EXPECT_TRUE(rubiApply(t, c, c.func("sin", x), x).isNull());

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
    // 2 + sin(x) stays Unevaluated rather than half-integrating.
    EXPECT_TRUE(rubiApply(
                    t, c,
                    c.add({c.number(std::int64_t{2}), c.func("sin", x)}), x)
                    .isNull());
    // Three-term Add (arity 3): every term integrates. NB a bare
    // linear term x or c*x does NOT (the matcher requires a Pow node
    // for x_^m_., unlike Mathematica's OneIdentity elision) - a known
    // limitation, honest Unevaluated.
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


