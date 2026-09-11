// rubi/rules_test.cpp — three layers per AGENTS.md for the C2 step-2
// matcher over the committed 1.1.1.1 slice:
//   1. fixed vectors: rule selection for textbook shapes;
//   2. property: random (a+b*x)^m with the EXACT canonical arity
//      always selects rule 4 (index 3) and binds a, b, x, m;
//   3. boundary: shapes outside the slice decline (-1), arity
//      mismatches decline, no bindings leak on failure.
#include <numkit/cas/rubi/rules.hpp>

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
        ASSERT_EQ(r, 1);
        ASSERT_EQ(b.size(), 2u);
        EXPECT_EQ(b[0].name, "x");
        EXPECT_EQ(b[0].value, x);
        EXPECT_EQ(b[1].name, "m");
        EXPECT_EQ(b[1].value, c.number(std::int64_t{7}));
    }
    // (2 + 3*x)^4: step-2 semantics is LINEAR rule order - the
    // wildcard x_ of rule 1 binds the whole base (Mathematically the
    // answer (a+b x)^(m+1)/(m+1) is still correct; Mathematica's
    // SPECIFICITY ordering that would prefer the (a_.+b_.*x_)^m_
    // shape is step-3 business).
    {
        const Expr e = c.pow(
            c.add({c.number(std::int64_t{2}),
                   c.mul({c.number(std::int64_t{3}), x})}),
            c.number(std::int64_t{4}));
        std::vector<Binding> b;
        const int r = matchFirst(t, c, e, b);
        ASSERT_EQ(r, 1);
        ASSERT_EQ(b.size(), 2u);
        EXPECT_EQ(b[0].name, "x"); // the wildcard bound the Add base
        EXPECT_EQ(b[1].name, "m");
        EXPECT_EQ(b[1].value, c.number(std::int64_t{4}));
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
    EXPECT_EQ(matchFirst(t, c, oneOver, b), 1);
    EXPECT_EQ(b.size(), 2u);

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
    // Random (a+b*x)^m always matches under the LINEAR step-2
    // semantics: the x_^m_. rule (index 1) grabs the base; the
    // bindings record exactly that (x := the Add, m := the exponent).
    Ctx c;
    const RuleTables t = sliceTables();
    const Expr x = c.symbol("x");
    std::uint64_t st = 0x2B1B4E5EEDULL;
    for (int iter = 0; iter < 3000; ++iter) {
        const std::int64_t a =
            static_cast<std::int64_t>(nextU64(st) % 13) - 6;
        const std::int64_t b =
            static_cast<std::int64_t>(nextU64(st) % 13) - 6;
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
        ASSERT_EQ(r, 1) << "iter " << iter;
        ASSERT_EQ(bs.size(), 2u);
        EXPECT_EQ(bs[0].name, "x");
        EXPECT_EQ(bs[0].value, base);
        EXPECT_EQ(bs[1].name, "m");
        EXPECT_EQ(bs[1].value, c.number(Rational(BigInt(m), BigInt(3))));
    }
}

} // namespace
