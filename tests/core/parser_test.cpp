// core/parser_test.cpp — three layers per AGENTS.md:
//   1. fixed vectors: parse(s) compared to nodes built through the Ctx
//      API — hash-consing makes equality exact node identity;
//   2. property: random Expr -> toString -> parseExpr in the SAME Ctx
//      reproduces the same node (fixed seed);
//   3. boundary: error inputs, error positions, dyadic decimal edges.
#include <numkit/cas/core/parser.hpp>

#include <gtest/gtest.h>

#include <cassert>
#include <cstdint>
#include <string>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Ctx;
using numkit::cas::Expr;
using numkit::cas::ParseError;
using numkit::cas::Rational;

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

Expr P(Ctx &c, const char *s) { return numkit::cas::parseExpr(c, s); }

Rational rat(std::int64_t p, std::int64_t q)
{
    return Rational(BigInt(p), BigInt(q));
}

TEST(ParserVector, NumbersFoldCanonically)
{
    Ctx c;
    EXPECT_EQ(P(c, "42"), c.number(std::int64_t{42}));
    EXPECT_EQ(P(c, "-42"), c.number(std::int64_t{-42}));
    EXPECT_EQ(P(c, "1/2"), c.number(rat(1, 2)));
    EXPECT_EQ(P(c, "2/4"), c.number(rat(1, 2)));
    EXPECT_EQ(P(c, "6/2"), c.number(std::int64_t{3}));
    EXPECT_EQ(P(c, "2^3^2"), c.number(std::int64_t{512}));
    EXPECT_EQ(P(c, "2^-1"), c.number(rat(1, 2)));
    EXPECT_EQ(P(c, "2^(-1)"), c.number(rat(1, 2)));
    EXPECT_EQ(P(c, "-2^2"), c.number(std::int64_t{-4}));
    EXPECT_EQ(P(c, "0.5"), c.number(rat(1, 2)));
    EXPECT_EQ(P(c, "2.25"), c.number(rat(9, 4)));
    EXPECT_EQ(P(c, "0.125"), c.number(rat(1, 8)));
    EXPECT_EQ(P(c, "12.5"), c.number(rat(25, 2)));
    EXPECT_EQ(P(c, "0.0009765625"), c.number(rat(1, 1024)));
    EXPECT_EQ(P(c, "0.0"), c.zero());
    EXPECT_EQ(P(c, "2.0"), c.number(std::int64_t{2}));
    EXPECT_EQ(c.toString(P(c, "99999999999999999999999999")),
              "99999999999999999999999999");
}

TEST(ParserVector, PrecedenceAndAssociativity)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    const Expr z = c.symbol("z");
    // Unary minus binds looser than '^': -x^2 == -(x^2).
    EXPECT_EQ(P(c, "-x^2"), c.neg(c.pow(x, c.number(std::int64_t{2}))));
    // ...but tighter than binary '+' and '*': -x + y == (-x) + y,
    // and an exponent sign never swallows the following term.
    EXPECT_EQ(P(c, "-x + y"), c.add({c.neg(x), y}));
    EXPECT_EQ(P(c, "2^-1 + 3"), c.number(rat(7, 2)));
    EXPECT_EQ(P(c, "x^-1 + 1"), P(c, "1/x + 1"));
    EXPECT_EQ(P(c, "y^-1*2"), P(c, "2/y"));
    // -x*y == (-x)*y grammatically; the canonical Mul makes it one
    // node with -(x*y), so both spellings intern identically.
    EXPECT_EQ(P(c, "-x*y"), P(c, "-(x*y)"));
    // '^' is right-associative.
    EXPECT_EQ(P(c, "x^y^z"), c.pow(x, c.pow(y, z)));
    // Left-associative '-'.
    EXPECT_EQ(P(c, "x-y-z"), c.add({x, c.neg(y), c.neg(z)}));
    // (x/y)/z and x/(y*z) both canonicalize to x*y^-1*z^-1.
    EXPECT_EQ(P(c, "x/y/z"), P(c, "x/(y*z)"));
    EXPECT_EQ(P(c, "2*x*y"), P(c, "x*y*2"));
    EXPECT_EQ(P(c, "1 + x"), P(c, "x + 1"));
    EXPECT_EQ(P(c, "(x+1)*(x-1)"),
              c.mul({c.add({x, c.number(std::int64_t{1})}),
                     c.add({x, c.number(std::int64_t{-1})})}));
    EXPECT_EQ(P(c, "(x)"), x);
    EXPECT_EQ(P(c, "((x))"), x);
    EXPECT_EQ(P(c, "x - x"), c.zero());
    // Like-term collection: -x -x +x collapse to -x, so 3 - x stays.
    EXPECT_EQ(P(c, "3 - x - x + x"), c.add({c.number(std::int64_t{3}), c.neg(x)}));
}

TEST(ParserVector, FunctionsAndSymbols)
{
    Ctx c;
    const Expr x = c.symbol("x");
    EXPECT_EQ(P(c, "sin(x)"), c.func("sin", x));
    EXPECT_EQ(P(c, "atan(x/2)"),
              c.func("atan", c.div(x, c.number(std::int64_t{2}))));
    // An identifier without '(' is a plain symbol, MATLAB-style.
    EXPECT_EQ(P(c, "sin"), c.symbol("sin"));
    // Whitespace between name and '(' still calls.
    EXPECT_EQ(P(c, "sin (x)"), c.func("sin", x));
    // Unknown names become Func nodes; the core owns the semantics.
    EXPECT_EQ(P(c, "foo(x)+1"),
              c.add({c.func("foo", x), c.number(std::int64_t{1})}));
    // The call binds tighter than '^': sin(x)^2 == (sin(x))^2.
    EXPECT_EQ(P(c, "sin(x)^2"), c.pow(c.func("sin", x), c.number(std::int64_t{2})));
    EXPECT_EQ(P(c, "sin(x^2)"), c.func("sin", c.pow(x, c.number(std::int64_t{2}))));
    // RootOf(...) parses as an ordinary Func, never the algebraic atom
    // (one argument only — commas are rejected by the grammar).
    EXPECT_EQ(c.kind(P(c, "RootOf(z^2 - 2)")), numkit::cas::NodeKind::Func);
}

TEST(ParserVector, PrintedCanonicalForms)
{
    Ctx c;
    EXPECT_EQ(c.toString(P(c, "1/2")), "1/2");
    EXPECT_EQ(c.toString(P(c, "x + 1 + 2")), "3 + x");
    EXPECT_EQ(c.toString(P(c, "2^3^2")), "512");
    EXPECT_EQ(c.toString(P(c, "0.5*x")), "1/2*x");
    EXPECT_EQ(c.toString(P(c, "0.25*x^2 + 0.5*x")), "1/4*x^2 + 1/2*x");
}

// ── property: print -> parse round-trip into the same node ──────

// The core asserts on 0^(negative) — same contract as division by a
// numeric zero — and the (u^a)^n = u^(a*n) rule can fold such a power
// in later (pow(pow(0,1/2),-2) -> 0^-1), so a numeric zero may only
// ever receive a small non-negative integer exponent here.
Expr powSafe(Ctx &c, Expr base, Expr exp)
{
    assert(c.kind(exp) == numkit::cas::NodeKind::Number);
    if (c.isZero(base)) {
        std::int64_t n = 0;
        const Rational &e = c.numberValue(exp);
        if (!(e.den() == BigInt(1)) || !e.num().fitsInt64(n) || n < 0)
            base = c.symbol("x");
    }
    return c.pow(base, exp);
}

Expr randomExpr(Ctx &c, std::uint64_t &st, int depth, const Expr &x,
                const Expr &y)
{
    const std::uint64_t r = nextU64(st);
    if (depth == 0 || r % 9 == 0) {
        switch ((r >> 8) % 3) {
        case 0: {
            const std::int64_t p =
                static_cast<std::int64_t>((r >> 16) % 19) - 9;
            const std::int64_t q =
                static_cast<std::int64_t>((r >> 32) % 4) * 3 + 1;
            return c.number(Rational(BigInt(p), BigInt(q)));
        }
        case 1: return x;
        default: return y;
        }
    }
    const Expr a = randomExpr(c, st, depth - 1, x, y);
    switch ((r >> 4) % 8) {
    case 0: return c.neg(a);
    case 1: return c.add({a, randomExpr(c, st, depth - 1, x, y)});
    case 2:
        return c.add({a, c.neg(randomExpr(c, st, depth - 1, x, y))});
    case 3: return c.mul({a, randomExpr(c, st, depth - 1, x, y)});
    case 4: {
        // Divide by a guaranteed non-zero constant or a symbol.
        if ((r >> 40) & 1)
            return c.div(a, (r >> 44) & 1 ? x : y);
        return c.div(
            a, c.number(rat(static_cast<std::int64_t>((r >> 44) % 5) - 2 == 0
                                ? 7
                                : static_cast<std::int64_t>((r >> 44) % 5) - 2,
                          3)));
    }
    case 5: {
        static const std::int64_t exps[] = {-3, -2, -1, 0, 1, 2, 3, 5};
        return powSafe(c, a, c.number(exps[(r >> 40) % 8]));
    }
    case 6: {
        static const Rational fracs[] = {rat(1, 2), rat(-1, 2), rat(1, 3),
                                         rat(3, 2)};
        return powSafe(c, a, c.number(fracs[(r >> 40) % 4]));
    }
    default: {
        static const char *names[] = {"sin", "cos", "tan", "atan", "exp", "log"};
        return c.func(names[(r >> 40) % 6], a);
    }
    }
}

TEST(ParserProperty, PrintParseRoundTripSameNode)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr y = c.symbol("y");
    std::uint64_t st = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20000; ++i) {
        const Expr e = randomExpr(c, st, 4, x, y);
        const std::string s = c.toString(e);
        Expr p;
        try {
            p = numkit::cas::parseExpr(c, s);
        } catch (const ParseError &err) {
            FAIL() << "round-trip parse failed on '" << s << "': " << err.what();
        }
        ASSERT_EQ(p, e) << "round-trip changed the node for '" << s << "'";
    }
}

TEST(ParserProperty, FractionalPowersRoundTrip)
{
    // Focused sweep: the printed forms of fractional/negative powers and
    // function applications are the classic precedence traps.
    Ctx c;
    const Expr x = c.symbol("x");
    const Expr f = c.func("sin", x);
    std::uint64_t st = 0xC0FFEE123456789ULL;
    for (int i = 0; i < 5000; ++i) {
        const std::int64_t num = static_cast<std::int64_t>(nextU64(st) % 7) - 3;
        const std::int64_t den =
            static_cast<std::int64_t>(nextU64(st) % 4) + 1;
        const Expr e = c.pow(nextU64(st) & 1 ? x : f,
                             c.number(Rational(BigInt(num), BigInt(den))));
        const std::string s = c.toString(e);
        ASSERT_EQ(numkit::cas::parseExpr(c, s), e)
            << "round-trip broke on '" << s << "'";
    }
}

// ── boundary: malformed input and error positions ───────────────

TEST(ParserBoundary, RejectsMalformedInput)
{
    Ctx c;
    const char *bad[] = {
        "",      "   ",    "x +",   "(x",    "x)",    "2 x",  "x y",
        "0.1",   "1.",     "1..2",  "sin(x", "()",    "x^",   ",",
        "1e5",   "@",      "2 & 3", "0.05",  "0.35",  "x 2",  "- ",
        "1/(",   "foo(,",  "3.4.5",
    };
    for (const char *s : bad) {
        try {
            numkit::cas::parseExpr(c, s);
            ADD_FAILURE() << "expected ParseError on: '" << s << "'";
        } catch (const ParseError &) {
        }
    }
}

TEST(ParserBoundary, ErrorPositionsAndMessages)
{
    Ctx c;
    try {
        numkit::cas::parseExpr(c, "x +");
        FAIL() << "expected ParseError";
    } catch (const ParseError &e) {
        EXPECT_EQ(e.pos(), 3);
    }
    try {
        numkit::cas::parseExpr(c, "@");
        FAIL() << "expected ParseError";
    } catch (const ParseError &e) {
        EXPECT_EQ(e.pos(), 0);
        EXPECT_NE(std::string(e.what()).find("unexpected character"),
                  std::string::npos);
    }
    try {
        numkit::cas::parseExpr(c, "x + 0.3");
        FAIL() << "expected ParseError";
    } catch (const ParseError &e) {
        EXPECT_EQ(e.pos(), 4);
        EXPECT_NE(std::string(e.what()).find("fraction"), std::string::npos);
    }
}

TEST(ParserBoundary, WhitespaceTolerated)
{
    Ctx c;
    const Expr x = c.symbol("x");
    EXPECT_EQ(P(c, "  x  "), x);
    EXPECT_EQ(P(c, "\tx\n"), x);
    EXPECT_EQ(P(c, "+x"), x);
    EXPECT_EQ(P(c, "- x"), c.neg(x));
    EXPECT_EQ(P(c, "1 / 2"), c.number(rat(1, 2)));
    EXPECT_EQ(P(c, "( 1 + x ) * 2"),
              c.mul({c.add({c.number(std::int64_t{1}), x}),
                     c.number(std::int64_t{2})}));
}

} // namespace
