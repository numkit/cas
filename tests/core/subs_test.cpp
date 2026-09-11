// core/subs_test.cpp — three layers per AGENTS.md for Ctx::subs:
//   1. fixed vectors: exact expected forms (canonical strings), incl.
//      folding after substitution and exponent-position hits;
//   2. properties (fixed seeds): identity on neutral/absent
//      substitutions, round-trips, commutation with print->parse;
//   3. boundary: whole-tree match, atom targets, from == to.
#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/core/parser.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <string>
#include <vector>

namespace {

using numkit::cas::Ctx;
using numkit::cas::Expr;
using numkit::cas::NodeKind;
using numkit::cas::parseExpr;
using numkit::cas::Rational;

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

TEST(SubsVector, ExactForms)
{
    Ctx c;
    const Expr x = c.symbol("x"), y = c.symbol("y");
    const Expr two = c.number(std::int64_t{2});

    // Numeric folding after the rebuild: x^2 with x -> 2 gives 4.
    EXPECT_EQ(c.subs(c.add({c.pow(x, two), y}), x, two),
              c.add({c.number(std::int64_t{4}), y}));
    // Function node replaced whole.
    EXPECT_EQ(c.subs(c.func("sin", x), c.func("sin", x), c.func("cos", x)),
              c.func("cos", x));
    // Hit inside the exponent position.
    EXPECT_EQ(c.subs(c.pow(x, two), two, c.number(std::int64_t{3})),
              c.pow(x, c.number(std::int64_t{3})));
    // Absent target: the SAME node comes back.
    const Expr e = c.add({c.pow(x, two), c.number(std::int64_t{1})});
    EXPECT_EQ(c.subs(e, c.symbol("z"), c.number(std::int64_t{5})), e);
    // from == to is the identity.
    EXPECT_EQ(c.subs(e, x, x), e);
    // Sub-expression target (x + 1) inside a product.
    const Expr sum = c.add({x, c.one()});
    EXPECT_EQ(c.subs(c.mul({sum, y}), sum, c.func("log", y)),
              c.mul({c.func("log", y), y}));
}

TEST(SubsVector, PrintedForms)
{
    Ctx c;
    EXPECT_EQ(c.toString(c.subs(parseExpr(c, "x^2 + y"), parseExpr(c, "x"),
                                parseExpr(c, "2"))),
              "4 + y");
    EXPECT_EQ(c.toString(c.subs(parseExpr(c, "x^2"), parseExpr(c, "2"),
                                parseExpr(c, "3"))),
              "x^3");
    EXPECT_EQ(
        c.toString(c.subs(parseExpr(c, "sin(x)*cos(x)"),
                          parseExpr(c, "sin(x)"), parseExpr(c, "u"))),
        "u*cos(x)"); // Symbol sorts before Func
}

TEST(SubsProperty, NeutralityAndRoundTrip)
{
    // For random trees: substituting a fresh symbol that never
    // occurs returns the SAME node; substituting x -> x is the
    // identity; and substituting x -> y then y -> x returns the
    // original when y did not occur in it.
    Ctx c;
    const Expr x = c.symbol("x"), y = c.symbol("y");
    const Expr z = c.symbol("z");
    std::uint64_t st = 0x5A5E5EED5A5BULL;
    const std::function<Expr(int)> randomExpr = [&](int depth) -> Expr {
        const std::uint64_t r = nextU64(st);
        if (depth == 0 || r % 9 == 0) {
            if ((r >> 8) % 2)
                return x;
            // avoid a numeric zero base: 0^(negative) asserts in the core
            int64_t num = static_cast<int64_t>((r >> 16) % 9) - 4;
            if (num == 0)
                num = 1;
            return c.number(Rational(numkit::cas::BigInt(num),
                                     numkit::cas::BigInt(3)));
        }
        const Expr a = randomExpr(depth - 1);
        switch ((r >> 4) % 5) {
        case 0: return c.neg(a);
        case 1: return c.add({a, randomExpr(depth - 1)});
        case 2: return c.mul({a, randomExpr(depth - 1)});
        case 3:
            // non-negative exponents only: intermediate folding can
            // produce a numeric zero (e.g. x + -x), and 0^negative
            // asserts in the core by contract
            return c.pow(a, c.number(
                                static_cast<std::int64_t>((r >> 40) % 4)));
        default:
            return c.func("sin", a);
        }
    };
    for (int iter = 0; iter < 5000; ++iter) {
        const Expr e = randomExpr(4);
        EXPECT_EQ(c.subs(e, z, x), e);   // absent target: same node
        EXPECT_EQ(c.subs(e, x, x), e);   // neutral substitution
        // x -> y -> x round-trips when y is fresh for the tree (x
        // trees built above never contain y).
        const Expr once = c.subs(e, x, y);
        EXPECT_EQ(c.subs(once, y, x), e);
    }
}

TEST(SubsProperty, PrintParseSurvival)
{
    // subs followed by print must round-trip through the parser.
    Ctx c;
    const Expr x = c.symbol("x");
    std::uint64_t st = 0xC0FFEE5EED5ULL;
    for (int iter = 0; iter < 3000; ++iter) {
        int64_t num = static_cast<int64_t>(nextU64(st) % 9) - 4;
        if (num == 0)
            num = 1; // no numeric-zero bases around negative powers
        const Expr e = c.add({c.mul({c.number(
            Rational(numkit::cas::BigInt(num),
                     numkit::cas::BigInt(3))),
            c.pow(x, c.number(std::int64_t{2}))}),
            c.func("sin", x)});
        const Expr s = c.subs(e, x, c.number(std::int64_t{7}));
        const std::string printed = c.toString(s);
        EXPECT_EQ(parseExpr(c, printed), s);
    }
}

TEST(SubsBoundary, AtomsAndWholeTree)
{
    Ctx c;
    const Expr x = c.symbol("x");
    // Whole tree matches immediately.
    EXPECT_EQ(c.subs(x, x, c.number(std::int64_t{9})),
              c.number(std::int64_t{9}));
    // Atoms as from-targets.
    EXPECT_EQ(c.subs(c.mul({c.number(std::int64_t{2}), x}),
                     c.number(std::int64_t{2}), c.number(std::int64_t{3})),
              c.mul({c.number(std::int64_t{3}), x}));
    // RootOf is an atom: matched whole, never descended into.
    const Expr root = c.rootOf({Rational(std::int64_t{-2}), Rational(),
                                Rational(std::int64_t{1})}, 0);
    EXPECT_EQ(c.subs(c.mul({root, x}), root, x), c.mul({x, x}));
    // Numeric-base folding: 1^2 collapses through the constructors.
    EXPECT_EQ(c.subs(c.pow(x, c.number(std::int64_t{2})), x, c.one()),
              c.one());
}

} // namespace
