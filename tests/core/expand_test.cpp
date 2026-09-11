// core/expand_test.cpp — three layers per AGENTS.md for Ctx::expand.
#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/core/parser.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Ctx;
using numkit::cas::Expr;
using numkit::cas::parseExpr;
using numkit::cas::Rational;

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

TEST(ExpandVector, ClassicShapes)
{
    Ctx c;
    EXPECT_EQ(c.toString(c.expand(parseExpr(c, "(x+1)*(x+2)"))),
              "2 + x^2 + 3*x");
    EXPECT_EQ(c.toString(c.expand(parseExpr(c, "(x+y)^3"))),
              "x^3 + y^3 + 3*x*y^2 + 3*y*x^2");
    // Distribution through a function factor.
    EXPECT_EQ(c.toString(c.expand(parseExpr(c, "(x+sin(x))*(x+2)"))),
              "x^2 + 2*x + 2*sin(x) + x*sin(x)");
    // Fractional powers stay folded.
    EXPECT_EQ(c.toString(c.expand(parseExpr(c, "(x+1)^(1/2)*(x+1)"))),
              "(1 + x)^(3/2)");
    // Negative integer power distributes multiplicatively over an
    // already-expanded product base.
    EXPECT_EQ(c.toString(c.expand(parseExpr(c, "(x*y)^-2"))),
              "x^-2*y^-2");
    // Idempotence on an already-expanded form.
    const Expr once = c.expand(parseExpr(c, "(x+2)*(x+3)*(x+5)"));
    EXPECT_EQ(c.expand(once), once);
}

TEST(ExpandProperty, EvaluationInvariant)
{
    // The strong semantic check: expansion must not change values.
    // For random (x+a)(x+b)(x+c)... trees, evalExact(expand(e)) ==
    // evalExact(e) at random rational points.
    Ctx c;
    const Expr x = c.symbol("x");
    std::uint64_t st = 0xE9F0A1D5EEDULL;
    for (int iter = 0; iter < 2000; ++iter) {
        const int nf = 1 + static_cast<int>(nextU64(st) % 3);
        std::vector<Expr> factors;
        for (int i = 0; i < nf; ++i) {
            const std::int64_t a =
                static_cast<std::int64_t>(nextU64(st) % 11) - 5;
            factors.push_back(
                c.add({x, c.number(Rational(BigInt(a), BigInt(3)))}));
        }
        Expr e = factors[0];
        for (std::size_t i = 1; i < factors.size(); ++i)
            e = c.mul({e, factors[i]});
        const Rational q(
            BigInt(static_cast<std::int64_t>(nextU64(st) % 9) - 4),
            BigInt(1 + static_cast<std::int64_t>(nextU64(st) % 3)));
        const std::vector<std::pair<std::string, Rational>> env{{"x", q}};
        Rational v1, v2;
        ASSERT_TRUE(c.evalExact(e, env, v1));
        ASSERT_TRUE(c.evalExact(c.expand(e), env, v2));
        EXPECT_EQ(v1, v2);
    }
}

TEST(ExpandBoundary, EdgeShapes)
{
    Ctx c;
    // Atoms and functions pass through.
    EXPECT_EQ(c.expand(c.symbol("x")), c.symbol("x"));
    EXPECT_EQ(c.toString(c.expand(parseExpr(c, "sin(x+1)"))), "sin(1 + x)");
    // (a+b)^0 / ^1 collapse before distribution.
    EXPECT_EQ(c.toString(c.expand(parseExpr(c, "(x+1)^1"))), "1 + x");
    // Nested double distribution.
    EXPECT_EQ(
        c.toString(c.expand(parseExpr(c, "((x+1)*(x+2))*(x+3)"))),
        c.toString(c.expand(parseExpr(c, "(x+1)*(x+2)*(x+3)"))));
}

} // namespace
