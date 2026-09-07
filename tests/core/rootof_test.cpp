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

Rational rr(std::uint64_t &state, int range)
{
    const std::int64_t n = static_cast<std::int64_t>(nextU64(state) % (2 * range + 1)) - range;
    const std::int64_t d =
        nextU64(state) % 3 == 0 ? static_cast<std::int64_t>(nextU64(state) % 4 + 1) : 1;
    return Rational(BigInt(n), BigInt(d));
}

} // namespace

TEST(RootOfAtom, ConstructionAndInterning)
{
    Ctx c;
    const std::vector<Rational> x3m2 = {Rational(std::int64_t{-2}), Rational(std::int64_t{0}),
                                         Rational(std::int64_t{0}), Rational(std::int64_t{1})};
    const Expr a = c.rootOf(x3m2, 0);
    const Expr b = c.rootOf(x3m2, 0);
    ASSERT_EQ(a, b); // identical content -> same node
    const std::size_t before = c.nodeCount();
    const Expr a2 = c.rootOf(x3m2, 0);
    EXPECT_EQ(a2, a);
    EXPECT_EQ(c.nodeCount(), before); // interning: no growth

    EXPECT_EQ(c.kind(a), NodeKind::RootOf);
    EXPECT_EQ(c.rootOfIndex(a), 0);
    EXPECT_EQ(c.rootOfPoly(a).size(), 4u);
    EXPECT_EQ(c.rootOfPoly(a).back(), Rational(std::int64_t{1}));

    // different root index -> different node
    const Expr c0 = c.rootOf(x3m2, 1);
    EXPECT_NE(a, c0);
    EXPECT_EQ(c.rootOfIndex(c0), 1);
}

TEST(RootOfAtom, CanonicalMonization)
{
    Ctx c;
    // 2x^2 - 4 is monicized to x^2 - 2 before interning.
    const std::vector<Rational> two{Rational(std::int64_t{-4}), Rational(std::int64_t{0}),
                                    Rational(std::int64_t{2})};
    const std::vector<Rational> one{Rational(std::int64_t{-2}), Rational(std::int64_t{0}),
                                    Rational(std::int64_t{1})};
    const Expr a = c.rootOf(two, 0);
    const Expr b = c.rootOf(one, 0);
    EXPECT_EQ(a, b);
    EXPECT_EQ(c.rootOfPoly(a).back(), Rational(std::int64_t{1}));
}

TEST(RootOfAtom, Printing)
{
    Ctx c;
    const std::vector<Rational> x3m2 = {Rational(std::int64_t{-2}), Rational(std::int64_t{0}),
                                         Rational(std::int64_t{0}), Rational(std::int64_t{1})};
    const Expr a = c.rootOf(x3m2, 0);
    EXPECT_EQ(c.toString(a), "RootOf(1*z^3 + 0*z^2 + 0*z + -2, 0)");
    // Inside arithmetic the atom binds like a symbol.
    const Expr x = c.symbol("x");
    EXPECT_EQ(c.toString(c.mul({x, a})), "x*RootOf(1*z^3 + 0*z^2 + 0*z + -2, 0)");
}

TEST(RootOfAtom, DifferentiatesToZero)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const std::vector<Rational> q{Rational(std::int64_t{1}), Rational(std::int64_t{0}),
                                  Rational(std::int64_t{1})};
    const Expr a = c.rootOf(q, 0); // root of z^2 + 1
    EXPECT_TRUE(c.isZero(c.diff(a, x)));
    EXPECT_EQ(c.diff(c.mul({a, x}), x), a); // constant multiple rule holds
}

TEST(RootOfAtom, CompareTotalOrder)
{
    Ctx c;
    const std::vector<Rational> p1{Rational(std::int64_t{-2}), Rational(std::int64_t{0}),
                                   Rational(std::int64_t{1})};               // z^2 - 2
    const std::vector<Rational> p2{Rational(std::int64_t{-3}), Rational(std::int64_t{0}),
                                   Rational(std::int64_t{1})};               // z^2 - 3
    const Expr a = c.rootOf(p1, 0);
    const Expr b = c.rootOf(p1, 1);
    const Expr d = c.rootOf(p2, 0);
    EXPECT_EQ(c.compare(a, a), 0);
    EXPECT_EQ(c.compare(a, b) < 0, true); // index order within same poly
    EXPECT_EQ(c.compare(b, a) > 0, true);
    // across polys: lexicographic on coefficients (constant -3 < -2)
    EXPECT_EQ(c.compare(d, a) < 0, true);
    EXPECT_EQ(c.compare(a, d) > 0, true);
    // deterministic sort of mixed roots
    std::vector<Expr> vs = {b, d, a, a};
    std::sort(vs.begin(), vs.end(), [&c](Expr u, Expr v) { return c.compare(u, v) < 0; });
    for (std::size_t i = 0; i + 1 < vs.size(); ++i)
        EXPECT_LE(c.compare(vs[i], vs[i + 1]), 0);
}

TEST(RootOfAtom, PropertyAlgebraAndRebuild)
{
    Ctx c;
    const Expr x = c.symbol("x");
    const std::vector<Rational> p{Rational(std::int64_t{-5}), Rational(std::int64_t{0}),
                                  Rational(std::int64_t{0}), Rational(std::int64_t{1})};
    std::uint64_t state = 0x600DCA5EED01ULL;
    for (int iter = 0; iter < 2000; ++iter) {
        const int i = static_cast<int>(nextU64(state) % 3);
        const int j = static_cast<int>(nextU64(state) % 3);
        const Expr a = c.rootOf(p, i);
        const Expr b = c.rootOf(p, j);
        EXPECT_EQ(a == b, i == j);
        // rebuild path: same construction returns the same node
        const std::size_t before = c.nodeCount();
        const Expr again = c.rootOf(p, i);
        EXPECT_EQ(again, a);
        EXPECT_EQ(c.nodeCount(), before);
        // atoms commute under multiplication with x
        EXPECT_EQ(c.mul({a, x}), c.mul({x, a}));
        EXPECT_TRUE(c.isZero(c.diff(a, x)));
    }
}
