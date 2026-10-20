// core/eval_test.cpp — three layers per AGENTS.md for the numeric
// groundwork of I1 item 20: Rational::fromDoubleBits (exact IEEE
// double -> Q) and Ctx::evalExact (exact rational evaluation of an
// expression, honest decline outside Q).
#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/poly/upoly.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include <cassert>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Ctx;
using numkit::cas::Expr;
using numkit::cas::NodeKind;
using numkit::cas::Rational;
using numkit::cas::UPoly;

// ── layer 1: fixed vectors (Python oracle: Fraction(float)) ────

TEST(FromDoubleBits, PythonOracle)
{
    struct Case
    {
        double v;
        const char *num;
        const char *den;
    };
    const Case cases[] = {
        {0.5, "1", "2"},
        {0.25, "1", "4"},
        {0.1, "3602879701896397", "36028797018963968"},
        {-3.0, "-3", "1"},
        {6.5, "13", "2"},
        {0.0, "0", "1"},
        {-0.0, "0", "1"},
        {1e-300,
         "6032057205060441",
         "603205720506044084884212454315773567705025225174850578179661"
         "506496162234449372729337097357813826574370822542501440083716"
         "481354049997906317910591959776695102219335509170789603485068"
         "403905907918039678834910609558429008744607641377146894047724"
         "155067075314551760293122439242402954742999382412988923515814"
         "5614364972941312"},
    };
    for (const Case &k : cases) {
        const Rational r = Rational::fromDoubleBits(k.v);
        BigInt n, d;
        EXPECT_TRUE(BigInt::tryParse(n, k.num));
        EXPECT_TRUE(BigInt::tryParse(d, k.den));
        EXPECT_EQ(r, Rational(std::move(n), std::move(d)))
            << "double " << k.v;
    }
}

TEST(FromDoubleBits, DenormalAndHuge)
{
    // Smallest denormal: 2^-1074 = 1 / 2^1074 (Python oracle).
    const Rational dn = Rational::fromDoubleBits(4.9406564584124654e-324);
    EXPECT_EQ(dn.num(), BigInt(1));
    EXPECT_EQ(dn.den(),
              BigInt::powUInt(BigInt(2), 1074));
    // 1e300 is an exact integer with a 301-digit numerator
    // (Python oracle, chunked for readability).
    const Rational r = Rational::fromDoubleBits(1e300);
    EXPECT_EQ(r.den(), BigInt(1));
    BigInt want;
    ASSERT_TRUE(BigInt::tryParse(
        want,
        std::string("100000000000000005250476025520442024870446858110815915491585"
                    "411551180245798890819578637137508044786404370444383288387817"
                    "694252323536043057564479218478670698284838720092657580373783"
                    "023379478809005936895323497079994508111903896764088007465274"
                    "278014249457925878882005684283811566947219638686545940054016"
                    "0")));
    EXPECT_EQ(r.num(), want);
}

TEST(EvalExact, FixedVectors)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const std::vector<std::pair<std::string, Rational>> env{{"x", Rational(std::int64_t{3})}};
    Rational out;

    ASSERT_TRUE(c.evalExact(c.add({c.pow(x, c.number(std::int64_t{2})),
                                   c.mul({c.number(std::int64_t{2}), x}),
                                   c.number(std::int64_t{1})}),
                            env, out));
    EXPECT_EQ(out, Rational(std::int64_t{16})); // 9 + 6 + 1

    // Negative power with a non-zero base.
    ASSERT_TRUE(c.evalExact(c.pow(x, c.number(std::int64_t{-2})), env, out));
    EXPECT_EQ(out, Rational(BigInt(1), BigInt(9)));

    // Trivial function points.
    ASSERT_TRUE(c.evalExact(c.func("exp", c.zero()), env, out));
    EXPECT_EQ(out, Rational(std::int64_t{1}));
    ASSERT_TRUE(c.evalExact(c.func("sin", c.zero()), env, out));
    EXPECT_EQ(out, Rational(std::int64_t{0}));
    ASSERT_TRUE(c.evalExact(c.func("asin", c.zero()), env, out));
    EXPECT_EQ(out, Rational(std::int64_t{0}));
    ASSERT_TRUE(c.evalExact(c.func("asinh", c.zero()), env, out));
    EXPECT_EQ(out, Rational(std::int64_t{0}));
    ASSERT_TRUE(c.evalExact(c.func("atanh", c.zero()), env, out));
    EXPECT_EQ(out, Rational(std::int64_t{0}));
    ASSERT_TRUE(c.evalExact(c.func("cosh", c.zero()), env, out));
    EXPECT_EQ(out, Rational(std::int64_t{1}));
    ASSERT_TRUE(c.evalExact(c.func("acos", c.one()), env, out));
    EXPECT_EQ(out, Rational(std::int64_t{0}));
    ASSERT_TRUE(c.evalExact(c.func("acosh", c.one()), env, out));
    EXPECT_EQ(out, Rational(std::int64_t{0}));

    // Honest declines.
    EXPECT_FALSE(c.evalExact(c.func("sin", x), env, out));      // sin(3)
    EXPECT_FALSE(c.evalExact(c.pow(c.number(std::int64_t{2}),
                                   c.number(Rational(BigInt(1), BigInt(2)))),
                             env, out));                         // 2^(1/2)
    EXPECT_FALSE(c.evalExact(c.symbol("y"), env, out));         // unresolved
    EXPECT_FALSE(c.evalExact(
        c.rootOf({Rational(std::int64_t{-2}), Rational(), Rational(std::int64_t{1})}, 0),
        env, out));                                              // RootOf
}

TEST(EvalExact, ZeroNegativePowerDeclines)
{
    // The 0^(-1) NODE cannot exist (the constructor asserts), but
    // evaluation can synthesize the shape: a numeric-zero base with
    // a symbol exponent whose value is negative.
    Ctx c;
    Rational out;
    const Expr y = c.symbol("y");
    const std::vector<std::pair<std::string, Rational>> env{
        {"y", Rational(std::int64_t{-1})}};
    EXPECT_FALSE(c.evalExact(c.pow(c.zero(), y), env, out));
}

// ── layer 2: property — agreement with UPoly::eval ────────────

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

TEST(EvalExact, MatchesUpolyEval)
{
    Ctx c;
    const Expr x = c.symbol("x");
    std::uint64_t st = 0xE9A1C0DE5EEDULL;
    for (int iter = 0; iter < 3000; ++iter) {
        std::vector<Rational> cs;
        const int deg = static_cast<int>(nextU64(st) % 5);
        for (int i = 0; i <= deg; ++i)
            cs.emplace_back(
                BigInt(static_cast<std::int64_t>(nextU64(st) % 17) - 8),
                BigInt(1 + static_cast<std::int64_t>(nextU64(st) % 4)));
        const UPoly p(cs);
        const Rational q(
            BigInt(static_cast<std::int64_t>(nextU64(st) % 13) - 6),
            BigInt(1 + static_cast<std::int64_t>(nextU64(st) % 4)));
        Rational out;
        ASSERT_TRUE(c.evalExact(numkit::cas::toExpr(c, p, x),
                                {{"x", q}}, out))
            << "deg " << deg;
        EXPECT_EQ(out, p.eval(q));
    }
}

// ── layer 3: boundary ─────────────────────────────────────────

TEST(EvalExact, Boundary)
{
    Ctx c;
    Rational out;
    // Empty expression list edge: a lone number evaluates with an
    // empty environment.
    ASSERT_TRUE(c.evalExact(c.number(Rational(BigInt(1), BigInt(3))), {}, out));
    EXPECT_EQ(out, Rational(BigInt(1), BigInt(3)));
    // A zero polynomial through many zeros.
    const Expr x = c.symbol("x");
    ASSERT_TRUE(c.evalExact(c.mul({x, c.zero()}), {{"x", Rational(std::int64_t{5})}}, out));
    EXPECT_EQ(out, Rational(std::int64_t{0}));
}

} // namespace
