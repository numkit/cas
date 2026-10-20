#include <numkit/cas/core/expr.hpp>

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

struct DiffTest : public ::testing::Test
{
    Ctx c;
    Expr x, y, z;

    void SetUp() override
    {
        x = c.symbol("x");
        y = c.symbol("y");
        z = c.symbol("z");
    }

    std::string dstr(Expr e)
    {
        const Expr d = c.diff(e, x);
        EXPECT_FALSE(d.isNull()) << "diff returned null for " << c.toString(e);
        return c.toString(d);
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
        return c.func(nextU64(state) % 2 ? "sin" : "log", rnd(depth - 1));
    }

    std::uint64_t state = 0xFEEDBEEFCAFE1234ULL;
};

} // namespace

TEST_F(DiffTest, BasicFormulas)
{
    EXPECT_EQ(dstr(x), "1");
    EXPECT_EQ(dstr(c.number(std::int64_t{5})), "0");
    EXPECT_EQ(dstr(y), "0");
    EXPECT_EQ(dstr(c.add({x, c.number(std::int64_t{3})})), "1");
    EXPECT_EQ(dstr(c.pow(x, c.number(std::int64_t{2}))), "2*x");
    EXPECT_EQ(dstr(c.pow(x, c.number(std::int64_t{3}))), "3*x^2");
    EXPECT_EQ(dstr(c.pow(x, c.number(half()))), "1/2*x^(-1/2)");
    EXPECT_EQ(dstr(c.div(c.one(), x)), "-x^-2");
    EXPECT_EQ(dstr(c.mul({c.number(std::int64_t{2}), x})), "2");
}

TEST_F(DiffTest, TranscendentalFunctions)
{
    EXPECT_EQ(dstr(c.func("exp", x)), "exp(x)");
    EXPECT_EQ(dstr(c.func("exp", c.mul({c.number(std::int64_t{2}), x}))),
              "2*exp(2*x)");
    EXPECT_EQ(dstr(c.func("log", x)), "x^-1");
    EXPECT_EQ(dstr(c.func("sin", x)), "cos(x)");
    EXPECT_EQ(dstr(c.func("cos", x)), "-sin(x)");
    EXPECT_EQ(dstr(c.func("tan", x)), "1 + tan(x)^2");
    EXPECT_EQ(dstr(c.func("atan", x)), "(1 + x^2)^-1");
    EXPECT_EQ(dstr(c.func("asin", x)), "(1 + -x^2)^(-1/2)");
    EXPECT_EQ(dstr(c.func("acos", x)), "-(1 + -x^2)^(-1/2)");
    EXPECT_EQ(dstr(c.func("sinh", x)), "cosh(x)");
    EXPECT_EQ(dstr(c.func("cosh", x)), "sinh(x)");
    EXPECT_EQ(dstr(c.func("tanh", x)), "1 + -tanh(x)^2");
    EXPECT_EQ(dstr(c.func("asinh", x)), "(1 + x^2)^(-1/2)");
    EXPECT_EQ(dstr(c.func("acosh", x)), "(-1 + x^2)^(-1/2)");
    EXPECT_EQ(dstr(c.func("atanh", x)), "(1 + -x^2)^-1");
}

TEST_F(DiffTest, ProductAndChainRules)
{
    EXPECT_EQ(dstr(c.mul({x, c.func("sin", x)})), "sin(x) + x*cos(x)");
    EXPECT_EQ(dstr(c.func("sin", c.pow(x, c.number(std::int64_t{2})))),
              "2*x*cos(x^2)");
    EXPECT_EQ(dstr(c.func("log", c.mul({x, y}))),
              "x^-1"); // d(log(x*y))/dx = (1/(x*y))*y = 1/x
    EXPECT_EQ(dstr(c.mul({x, y})), "y");
}

TEST_F(DiffTest, PowGeneralCases)
{
    EXPECT_EQ(dstr(c.pow(c.number(std::int64_t{2}), x)), "2^x*log(2)");
    EXPECT_EQ(dstr(c.pow(x, x)), "x^x*(1 + log(x))");
    EXPECT_EQ(dstr(c.pow(c.pow(x, y), c.number(std::int64_t{2}))),
              "2*y*x^-1*(x^y)^2"); // (x^y)^2 stays grouped: y is not a Number
}

TEST_F(DiffTest, HigherOrderDerivatives)
{
    EXPECT_EQ(dstr(c.diff(c.pow(x, c.number(std::int64_t{3})), x)), "6*x");
    EXPECT_EQ(dstr(c.diff(c.func("sin", x), x)), "-sin(x)");
    EXPECT_EQ(dstr(c.diff(c.mul({x, x}), x)), "2");
}

TEST_F(DiffTest, ConstantArgumentsFoldToZero)
{
    // Guards in the diff rules must not build singular intermediate nodes
    // (pow(0, -1), log(0) inside a zero product).
    EXPECT_EQ(dstr(c.func("log", c.zero())), "0");
    EXPECT_EQ(dstr(c.func("log", c.number(std::int64_t{5}))), "0");
    EXPECT_EQ(dstr(c.func("log", y)), "0");
    EXPECT_EQ(dstr(c.pow(c.number(std::int64_t{8}), c.number(half()))), "0");
    EXPECT_EQ(dstr(c.pow(c.number(std::int64_t{2}), y)), "0");
}

TEST_F(DiffTest, MemoizedAndInterned)
{
    const Expr f = c.mul({c.add({x, c.one()}), c.func("sin", x)});
    const Expr d1 = c.diff(f, x);
    const std::size_t before = c.nodeCount();
    const Expr d2 = c.diff(f, x);
    EXPECT_EQ(d1, d2);
    EXPECT_EQ(c.nodeCount(), before);
    EXPECT_EQ(d1, c.diff(clone(f), x));
}

namespace {

struct DiffPropertyTest : public DiffTest
{
};

} // namespace

TEST_F(DiffPropertyTest, LinearityAndProductRule)
{
    // The pairwise product identity d(a*b) = d(a)*b + a*d(b) holds as node
    // identity only when neither operand is itself a Mul: mul(a, b) then
    // keeps exactly two children. With a Mul operand the n-ary rule
    // distributes over the flattened factors — equal as functions, but a
    // different canonical node (the canonical form does not distribute
    // Mul over Add by design).
    const auto nonMul = [this](Expr e) { return c.kind(e) != NodeKind::Mul; };
    for (int iter = 0; iter < 5000; ++iter) {
        const Expr a = rnd(3);
        const Expr b = rnd(3);
        if (!nonMul(a) || !nonMul(b))
            continue;
        const Expr da = c.diff(a, x);
        const Expr db = c.diff(b, x);
        ASSERT_FALSE(da.isNull());
        ASSERT_FALSE(db.isNull());

        ASSERT_EQ(c.diff(c.add({a, b}), x), c.add({da, db}))
            << c.toString(a) << " , " << c.toString(b);
        ASSERT_EQ(c.diff(c.mul({a, b}), x),
                  c.add({c.mul({da, b}), c.mul({a, db})}))
            << c.toString(a) << " , " << c.toString(b);
    }
}

TEST_F(DiffPropertyTest, NaryProductRule)
{
    const auto nonMul = [this](Expr e) { return c.kind(e) != NodeKind::Mul; };
    for (int iter = 0; iter < 5000; ++iter) {
        const Expr a = rnd(2);
        const Expr b = rnd(2);
        const Expr d = rnd(2);
        if (!nonMul(a) || !nonMul(b) || !nonMul(d))
            continue;
        const Expr t = c.mul({a, b, d});
        const Expr da = c.diff(a, x);
        const Expr db = c.diff(b, x);
        const Expr dd = c.diff(d, x);
        const Expr expected = c.add({c.mul({da, b, d}), c.mul({a, db, d}),
                                     c.mul({a, b, dd})});
        ASSERT_EQ(c.diff(t, x), expected)
            << c.toString(t) << " -> " << c.toString(c.diff(t, x))
            << " vs " << c.toString(expected);
    }
}

TEST_F(DiffPropertyTest, IndependentVariableGivesZero)
{
    const Expr w = c.symbol("w"); // never generated by rnd
    for (int iter = 0; iter < 3000; ++iter) {
        const Expr e = rnd(4);
        ASSERT_EQ(c.diff(e, w), c.zero()) << c.toString(e);
    }
}

TEST_F(DiffPropertyTest, DiffOfCloneIsIdentical)
{
    for (int iter = 0; iter < 3000; ++iter) {
        const Expr e = rnd(4);
        const Expr d1 = c.diff(e, x);
        const std::size_t before = c.nodeCount();
        const Expr d2 = c.diff(clone(e), x);
        ASSERT_EQ(d1, d2) << c.toString(e);
        ASSERT_EQ(c.nodeCount(), before);
    }
}
