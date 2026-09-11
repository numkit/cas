#include <numkit/cas/core/expr.hpp>

#include <algorithm>

#include <gtest/gtest.h>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Ctx;
using numkit::cas::Expr;
using numkit::cas::NodeKind;
using numkit::cas::Rational;

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

Rational half()
{
    return Rational(std::int64_t{1}, BigInt(2));
}

struct ExprTest : public ::testing::Test
{
    Ctx c;
    Expr x, y, z;

    void SetUp() override
    {
        x = c.symbol("x");
        y = c.symbol("y");
        z = c.symbol("z");
    }

    std::string str(Expr e) const { return c.toString(e); }

    Expr clone(Expr e)
    {
        switch (c.kind(e)) {
        case NodeKind::Number:
            return c.number(c.numberValue(e));
        case NodeKind::Symbol:
            return c.symbol(c.symbolName(e));
        case NodeKind::Pow:
            return c.pow(clone(c.child(e, 0)), clone(c.child(e, 1)));
        case NodeKind::Func:
            return c.func(c.funcName(e), clone(c.child(e, 0)));
        case NodeKind::Add:
        case NodeKind::Mul: {
            std::vector<Expr> cs;
            for (std::size_t i = 0; i < c.childCount(e); ++i)
                cs.push_back(clone(c.child(e, i)));
            return c.kind(e) == NodeKind::Add ? c.add(cs) : c.mul(cs);
        }
        }
        return {};
    }
};

} // namespace

TEST_F(ExprTest, AtomBasics)
{
    EXPECT_EQ(str(c.number(std::int64_t{7})), "7");
    EXPECT_EQ(str(c.number(half())), "1/2");
    EXPECT_EQ(str(x), "x");
    EXPECT_EQ(c.kind(x), NodeKind::Symbol);
    EXPECT_EQ(c.kind(c.number(std::int64_t{0})), NodeKind::Number);
    EXPECT_TRUE(Expr().isNull());
    EXPECT_FALSE(x.isNull());
    EXPECT_EQ(c.symbolName(x), "x");
    EXPECT_EQ(c.childCount(x), 0u);
}

TEST_F(ExprTest, NumberInterningCanonicalizes)
{
    EXPECT_EQ(c.number(Rational(BigInt(2), BigInt(4))), c.number(half()));
}

TEST_F(ExprTest, AddCanonicalFolding)
{
    EXPECT_EQ(str(c.add({})), "0");
    EXPECT_EQ(str(c.add({x})), "x");
    EXPECT_EQ(str(c.add({x, c.zero()})), "x");
    EXPECT_EQ(str(c.add({c.number(std::int64_t{1}), c.number(std::int64_t{2})})),
              "3");
    EXPECT_EQ(str(c.add({c.number(std::int64_t{1}), c.number(std::int64_t{2}), x})),
              "3 + x");
    EXPECT_EQ(str(c.add({x, x})), "2*x");
    EXPECT_EQ(str(c.add({x, x, x})), "3*x");
    EXPECT_EQ(str(c.add({x, y, x, y, y})), "2*x + 3*y");
    EXPECT_EQ(str(c.add({c.add({c.number(std::int64_t{1}), x}), y})), "1 + x + y");
    EXPECT_EQ(str(c.add({c.add({x, y}), c.add({z, x})})), "y + z + 2*x");
    EXPECT_EQ(str(c.add({c.number(std::int64_t{1}), c.number(std::int64_t{-1})})),
              "0");
    // Like-term collection merges coefficient forms, not only equal runs.
    EXPECT_EQ(str(c.add({y, y, c.mul({c.number(std::int64_t{2}), y})})), "4*y");
    EXPECT_EQ(str(c.add({c.mul({c.number(std::int64_t{3}), x}),
                         c.mul({c.number(std::int64_t{5}), x})})),
              "8*x");
    EXPECT_EQ(str(c.add({x, c.neg(x)})), "0");
    EXPECT_EQ(str(c.add({x, c.neg(x), y})), "y");
    EXPECT_EQ(str(c.add({c.mul({c.number(std::int64_t{2}), x, y}), x, y})),
              "x + y + 2*x*y");
}

TEST_F(ExprTest, MulCanonicalFolding)
{
    EXPECT_EQ(str(c.mul({})), "1");
    EXPECT_EQ(str(c.mul({x})), "x");
    EXPECT_EQ(str(c.mul({x, c.one()})), "x");
    EXPECT_EQ(str(c.mul({x, c.zero()})), "0");
    EXPECT_EQ(str(c.mul({c.number(std::int64_t{2}), c.number(std::int64_t{3}), x})),
              "6*x");
    EXPECT_EQ(str(c.mul({c.number(half()), x})), "1/2*x");
    EXPECT_EQ(str(c.mul({x, x})), "x^2");
    EXPECT_EQ(str(c.mul({x, x, x})), "x^3");
    EXPECT_EQ(str(c.mul({x, y, x, y, y})), "x^2*y^3");
    EXPECT_EQ(str(c.mul({c.mul({c.number(std::int64_t{2}), x}),
                         c.number(std::int64_t{3})})),
              "6*x");
    EXPECT_EQ(str(c.mul({x, y, z})), "x*y*z");
    // Like-base collection merges exponent forms, not only equal runs.
    EXPECT_EQ(str(c.mul({x, x, c.pow(x, c.number(std::int64_t{2}))})), "x^4");
    EXPECT_EQ(str(c.mul({c.pow(x, c.number(std::int64_t{3})),
                         c.pow(x, c.number(std::int64_t{5}))})),
              "x^8");
    EXPECT_EQ(str(c.mul({x, c.div(c.one(), x)})), "1");
    EXPECT_EQ(str(c.mul({c.mul({c.number(std::int64_t{2}), x}),
                         c.mul({c.number(std::int64_t{3}), x})})),
              "6*x^2");
    // Rational exponents of equal bases combine exactly.
    EXPECT_EQ(str(c.mul({c.pow(x, c.number(half())), c.pow(x, c.number(half()))})),
              "x");
}

TEST_F(ExprTest, NegAndDiv)
{
    EXPECT_EQ(str(c.neg(x)), "-x");
    EXPECT_EQ(str(c.neg(c.number(std::int64_t{2}))), "-2");
    EXPECT_EQ(str(c.div(c.one(), x)), "x^-1");
    EXPECT_EQ(str(c.div(x, c.number(std::int64_t{2}))), "1/2*x");
    EXPECT_EQ(str(c.div(c.one(), c.number(std::int64_t{4}))), "1/4");
    EXPECT_EQ(str(c.mul({c.neg(c.one()), x, y})), "-x*y");
}

TEST_F(ExprTest, PowNumericFolding)
{
    EXPECT_EQ(str(c.pow(x, c.zero())), "1");
    EXPECT_EQ(str(c.pow(x, c.one())), "x");
    EXPECT_EQ(str(c.pow(c.number(std::int64_t{2}), c.number(std::int64_t{10}))),
              "1024");
    EXPECT_EQ(str(c.pow(c.number(std::int64_t{2}), c.number(std::int64_t{100}))),
              "1267650600228229401496703205376");
    EXPECT_EQ(str(c.pow(c.number(std::int64_t{2}), c.number(std::int64_t{-2}))),
              "1/4");
    EXPECT_EQ(str(c.pow(c.number(half()), c.number(std::int64_t{-1}))), "2");
    EXPECT_EQ(str(c.pow(c.number(half()), c.number(std::int64_t{3}))), "1/8");
    // Beyond the folding bound the Pow stays symbolic, deterministically.
    EXPECT_EQ(str(c.pow(c.number(std::int64_t{2}),
                        c.number(std::int64_t{1000000}))),
              "2^1000000");
    EXPECT_EQ(c.kind(c.pow(c.number(std::int64_t{2}),
                           c.number(std::int64_t{1000000}))),
              NodeKind::Pow);
    // Rational (non-integer) exponents stay symbolic even on numbers.
    EXPECT_EQ(str(c.pow(c.number(std::int64_t{8}), c.number(half()))), "8^(1/2)");
}

TEST_F(ExprTest, PowStructuralRules)
{
    EXPECT_EQ(str(c.pow(x, c.number(std::int64_t{2}))), "x^2");
    EXPECT_EQ(str(c.pow(c.pow(x, c.number(std::int64_t{2})),
                        c.number(std::int64_t{3}))),
              "x^6");
    EXPECT_EQ(str(c.pow(c.mul({x, y}), c.number(std::int64_t{2}))), "x^2*y^2");
    EXPECT_EQ(str(c.pow(c.mul({c.number(std::int64_t{2}), x}),
                        c.number(std::int64_t{-1}))),
              "1/2*x^-1");
    EXPECT_EQ(str(c.pow(c.add({x, c.one()}), c.number(std::int64_t{2}))),
              "(1 + x)^2");
    EXPECT_EQ(str(c.pow(c.add({x, y}), c.one())), "x + y");
    EXPECT_EQ(str(c.pow(c.pow(x, c.number(half())), c.number(std::int64_t{2}))),
              "x");
}

TEST_F(ExprTest, PrintingPrecedence)
{
    EXPECT_EQ(str(c.mul({x, c.pow(c.add({x, c.one()}), c.number(std::int64_t{2}))})),
              "x*(1 + x)^2");
    EXPECT_EQ(str(c.pow(c.number(half()), x)), "(1/2)^x");
    EXPECT_EQ(str(c.add({c.mul({c.number(std::int64_t{2}), x}),
                         c.pow(x, c.number(std::int64_t{2}))})),
              "x^2 + 2*x");
    EXPECT_EQ(str(c.func("sin", c.add({x, c.one()}))), "sin(1 + x)");
    EXPECT_EQ(str(c.pow(c.func("sin", x), c.number(std::int64_t{2}))),
              "sin(x)^2");
    EXPECT_EQ(str(c.mul({c.pow(x, c.number(std::int64_t{2})), y})), "y*x^2");
    EXPECT_EQ(str(c.pow(c.pow(x, c.number(std::int64_t{2})),
                        c.number(std::int64_t{3}))),
              "x^6");
}

// Guard for bugs/opened/core/expr-neg-pow-base-print.md: a negative
// numeric Pow base must keep parens — without them the string means
// -(base^exp) under the parser's precedence, a different branch.
TEST_F(ExprTest, NegativePowBaseKeepsParens)
{
    const Expr e = c.pow(c.number(Rational(std::int64_t{-9})),
                         c.number(Rational(BigInt(-1), BigInt(2))));
    EXPECT_EQ(str(e), "(-9)^(-1/2)");
    // Positive numeric bases and negative exponents are unaffected.
    EXPECT_EQ(str(c.pow(c.number(std::int64_t{9}), c.number(half()))),
              "9^(1/2)");
    EXPECT_EQ(str(c.pow(x, c.number(std::int64_t{-2}))), "x^-2");
}

TEST_F(ExprTest, InterningAndDeterminism)
{
    const Expr a = c.mul({c.add({x, c.one()}), c.add({x, c.one()})});
    const std::size_t nodesBefore = c.nodeCount();
    const Expr b = c.mul({c.add({x, c.one()}), c.add({x, c.one()})});
    EXPECT_EQ(a, b);
    EXPECT_EQ(c.nodeCount(), nodesBefore);

    EXPECT_EQ(c.add({x, y, z}), c.add({z, y, x}));
    EXPECT_EQ(c.mul({x, y, z}), c.mul({z, x, y}));
    EXPECT_EQ(c.add({c.mul({x, y}), z}), c.add({z, c.mul({y, x})}));
    EXPECT_EQ(c.add({x, y, x}), c.add({y, c.add({x, x})}));
    EXPECT_EQ(c.mul({x, y, x}), c.mul({c.mul({x, y}), x}));
}

TEST_F(ExprTest, CompareIsTotalOrder)
{
    const Expr a = c.add({x, c.one()});
    const Expr b = c.mul({x, y});
    const Expr d = c.pow(x, c.number(std::int64_t{2}));
    const Expr f = c.func("sin", x);

    EXPECT_EQ(c.compare(a, a), 0);
    EXPECT_EQ(c.compare(a, b), -c.compare(b, a));
    EXPECT_EQ(c.compare(c.number(std::int64_t{5}), c.number(std::int64_t{6})), -1);
    EXPECT_EQ(c.compare(c.number(std::int64_t{5}), x), -1); // Number < Symbol
    EXPECT_EQ(c.compare(x, y), -1);                          // by name

    std::vector<Expr> v = {a, b, d, f, x, y, c.zero(), c.one(), c.add({x, y}),
                           c.mul({x, c.number(std::int64_t{3})})};
    std::sort(v.begin(), v.end(),
              [this](Expr p, Expr q) { return c.compare(p, q) < 0; });
    EXPECT_TRUE(std::is_sorted(v.begin(), v.end(), [this](Expr p, Expr q) {
        return c.compare(p, q) < 0;
    }));
    for (std::size_t i = 0; i + 1 < v.size(); ++i)
        EXPECT_LE(c.compare(v[i], v[i + 1]), 0);
}

namespace {

struct RandomExprTest : public ::testing::Test
{
    Ctx c;
    std::uint64_t state = 0xABCDEF0123456789ULL;

    Expr rnd(int depth)
    {
        const std::uint64_t roll = nextU64(state) % 100;
        if (depth <= 0 || roll < 30) {
            if (nextU64(state) % 2)
                return c.symbol(nextU64(state) % 2 ? "x" : "y");
            return c.number(static_cast<std::int64_t>(nextU64(state) % 17) - 8);
        }
        if (roll < 55)
            return c.add({rnd(depth - 1), rnd(depth - 1), rnd(depth - 1)});
        if (roll < 75)
            return c.mul({rnd(depth - 1), rnd(depth - 1)});
        if (roll < 85)
            return c.pow(rnd(depth - 1),
                         c.number(static_cast<std::int64_t>(nextU64(state) % 4)));
        if (roll < 93)
            return c.func(nextU64(state) % 2 ? "sin" : "log", rnd(depth - 1));
        return c.neg(rnd(depth - 1));
    }

    Expr clone(Expr e)
    {
        switch (c.kind(e)) {
        case NodeKind::Number:
            return c.number(c.numberValue(e));
        case NodeKind::Symbol:
            return c.symbol(c.symbolName(e));
        case NodeKind::Pow:
            return c.pow(clone(c.child(e, 0)), clone(c.child(e, 1)));
        case NodeKind::Func:
            return c.func(c.funcName(e), clone(c.child(e, 0)));
        case NodeKind::Add:
        case NodeKind::Mul: {
            std::vector<Expr> cs;
            for (std::size_t i = 0; i < c.childCount(e); ++i)
                cs.push_back(clone(c.child(e, i)));
            return c.kind(e) == NodeKind::Add ? c.add(cs) : c.mul(cs);
        }
        }
        return {};
    }
};

} // namespace

TEST_F(RandomExprTest, CloneRebuildIsIdentical)
{
    for (int iter = 0; iter < 5000; ++iter) {
        const Expr e = rnd(4);
        const std::size_t before = c.nodeCount();
        const Expr again = clone(e);
        ASSERT_EQ(again, e) << "iter " << iter << ": " << c.toString(e)
                            << " vs " << c.toString(again);
        ASSERT_EQ(c.nodeCount(), before) << "interner grew on rebuild";
        ASSERT_EQ(c.toString(again), c.toString(e));
        ASSERT_EQ(c.compare(again, e), 0);
    }
}

TEST_F(RandomExprTest, CompareAntisymmetryAndIdentity)
{
    for (int iter = 0; iter < 5000; ++iter) {
        const Expr a = rnd(4);
        const Expr b = rnd(4);
        const int ab = c.compare(a, b);
        const int ba = c.compare(b, a);
        ASSERT_EQ(ab, -ba) << c.toString(a) << " vs " << c.toString(b);
        ASSERT_EQ(ab == 0, a == b);
    }
}

TEST_F(RandomExprTest, ToStringDeterministic)
{
    for (int iter = 0; iter < 2000; ++iter) {
        const Expr e = rnd(5);
        ASSERT_EQ(c.toString(e), c.toString(e));
    }
}

TEST_F(RandomExprTest, RepeatedBuildIsIdentical)
{
    // Build the same random subexpression twice through different paths
    // (direct reuse vs rebuild via clone) — canonical form must coincide.
    for (int iter = 0; iter < 3000; ++iter) {
        const Expr a = rnd(3);
        const Expr b = rnd(3);
        const Expr e1 = c.add({a, b, a});
        const Expr e2 = c.add({clone(a), clone(b), clone(a)});
        ASSERT_EQ(e1, e2) << c.toString(e1) << " vs " << c.toString(e2);
    }
}

// Guard for bugs/opened/core/div-zero-denominator-release-node.md:
// a numeric-zero denominator / zero-to-negative-power must never
// produce a live node in Release (the Debug assert is the contract
// there; this guard runs the NDEBUG semantics).
TEST_F(ExprTest, ZeroDenominatorIsNullInRelease)
{
#ifdef NDEBUG
    const Expr e = c.div(x, c.zero());
    EXPECT_TRUE(e.isNull());
    const Expr p = c.pow(c.zero(), c.number(std::int64_t{-2}));
    EXPECT_TRUE(p.isNull());
#else
    GTEST_SKIP() << "Debug: the assert is the contract";
#endif
}
