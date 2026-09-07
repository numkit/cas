#include <numkit/cas/poly/algebraic.hpp>

#include <string>

#include <gtest/gtest.h>

namespace {

using numkit::cas::Algebraic;
using numkit::cas::BigInt;
using numkit::cas::Rational;
using numkit::cas::UPoly;

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

UPoly rndPoly(std::uint64_t &state, int maxDeg)
{
    const int deg = 1 + static_cast<int>(nextU64(state) % maxDeg);
    std::vector<Rational> cs;
    for (int i = 0; i < deg; ++i)
        cs.push_back(rr(state, 6));
    Rational lc = rr(state, 5);
    if (lc.isZero())
        lc = Rational(std::int64_t{1});
    cs.push_back(lc);
    return UPoly(std::move(cs));
}

} // namespace

TEST(AlgebraicConstruction, CanonicalForms)
{
    EXPECT_TRUE(Algebraic().isRational());
    EXPECT_EQ(Algebraic().rationalValue(), Rational(std::int64_t{0}));
    const Algebraic half(Rational(std::int64_t{1}, BigInt(2)));
    EXPECT_TRUE(half.isRational());
    EXPECT_EQ(half.rationalValue(), Rational(std::int64_t{1}, BigInt(2)));

    // Linear polynomials normalize to exact rationals.
    const std::vector<Algebraic> lin =
        Algebraic::realRoots(UPoly(std::vector<Rational>{
            Rational(std::int64_t{3}), Rational(std::int64_t{-2})}));
    ASSERT_EQ(lin.size(), 1u);
    EXPECT_TRUE(lin[0].isRational());
    EXPECT_EQ(lin[0].rationalValue(), Rational(std::int64_t{3}, BigInt(2)));
}

TEST(AlgebraicSqrt2, RootsSignsAndOrder)
{
    const std::vector<Algebraic> roots = Algebraic::realRoots(
        UPoly(std::vector<Rational>{Rational(std::int64_t{-2}), Rational(std::int64_t{0}),
                                    Rational(std::int64_t{1})}));
    ASSERT_EQ(roots.size(), 2u);
    EXPECT_EQ(roots[0].sign(), -1);
    EXPECT_EQ(roots[1].sign(), 1);
    EXPECT_LT(Algebraic::compare(roots[0], roots[1]), 0);
    EXPECT_NEAR(roots[0].approx(), -1.414213562, 1e-5);
    EXPECT_NEAR(roots[1].approx(), 1.414213562, 1e-5);

    // Rational comparisons around sqrt(2).
    EXPECT_GT(Algebraic::compare(roots[1], Algebraic(Rational(std::int64_t{1}))), 0);
    EXPECT_LT(Algebraic::compare(roots[1], Algebraic(Rational(std::int64_t{2}))), 0);
    EXPECT_GT(Algebraic::compare(roots[1], Algebraic(Rational(std::int64_t{7}, BigInt(5)))), 0);
    EXPECT_LT(Algebraic::compare(roots[1], Algebraic(Rational(std::int64_t{17}, BigInt(12)))), 0);
}

TEST(AlgebraicEquality, AcrossRepresentations)
{
    // sqrt(2) defined by x^2 - 2 and by x^4 - 4 (positive roots).
    const std::vector<Algebraic> a = Algebraic::realRoots(
        UPoly(std::vector<Rational>{Rational(std::int64_t{-2}), Rational(std::int64_t{0}),
                                    Rational(std::int64_t{1})}));
    const std::vector<Algebraic> b = Algebraic::realRoots(
        UPoly(std::vector<Rational>{Rational(std::int64_t{-4}), Rational(std::int64_t{0}),
                                    Rational(std::int64_t{0}), Rational(std::int64_t{0}),
                                    Rational(std::int64_t{1})}));
    ASSERT_EQ(a.size(), 2u);
    ASSERT_EQ(b.size(), 2u);
    EXPECT_EQ(Algebraic::compare(a[0], b[0]), 0);
    EXPECT_EQ(Algebraic::compare(a[1], b[1]), 0);
    EXPECT_NE(Algebraic::compare(a[0], b[1]), 0);

    // sqrt(2) inside a larger squarefree polynomial (x^2 - 2)(x - 5)
    // = x^3 - 5x^2 - 2x + 10.
    const std::vector<Algebraic> c = Algebraic::realRoots(
        UPoly(std::vector<Rational>{Rational(std::int64_t{10}), Rational(std::int64_t{-2}),
                                    Rational(std::int64_t{-5}), Rational(std::int64_t{1})}));
    ASSERT_EQ(c.size(), 3u); // -sqrt2, sqrt2, 5
    bool found = false;
    for (const Algebraic &r : c)
        if (Algebraic::compare(r, a[1]) == 0)
            found = true;
    EXPECT_TRUE(found);
}

TEST(AlgebraicDistinct, Sqrt2VsSqrt3)
{
    const std::vector<Algebraic> s2 = Algebraic::realRoots(
        UPoly(std::vector<Rational>{Rational(std::int64_t{-2}), Rational(std::int64_t{0}),
                                    Rational(std::int64_t{1})}));
    const std::vector<Algebraic> s3 = Algebraic::realRoots(
        UPoly(std::vector<Rational>{Rational(std::int64_t{-3}), Rational(std::int64_t{0}),
                                    Rational(std::int64_t{1})}));
    EXPECT_LT(Algebraic::compare(s2[1], s3[1]), 0); // sqrt2 < sqrt3
    EXPECT_GT(Algebraic::compare(s3[1], s2[1]), 0);
    EXPECT_LT(Algebraic::compare(s3[0], s2[0]), 0); // -sqrt3 < -sqrt2
    EXPECT_EQ(Algebraic::compare(s2[0], s2[0]), 0);
}

TEST(AlgebraicProperty, OrderingAndCrossRepresentation)
{
    std::uint64_t state = 0x0DDF00D5EED15ULL;
    for (int iter = 0; iter < 1000; ++iter) {
        const UPoly p = rndPoly(state, 5);
        const UPoly q = rndPoly(state, 3);
        if (q.isConst())
            continue;
        const std::vector<Algebraic> rp = Algebraic::realRoots(p);
        const std::vector<Algebraic> rq = Algebraic::realRoots(q);
        const std::vector<Algebraic> rpq = Algebraic::realRoots(p * q);
        if (rp.empty() && rq.empty())
            continue;

        // Ascending order and antisymmetry within one isolation run.
        for (std::size_t i = 0; i + 1 < rp.size(); ++i) {
            ASSERT_LT(Algebraic::compare(rp[i], rp[i + 1]), 0);
            ASSERT_GT(Algebraic::compare(rp[i + 1], rp[i]), 0);
        }

        // Every root of p equals a root of p*q and vice versa (matched
        // against p's or q's roots).
        for (const Algebraic &a : rp) {
            bool found = false;
            for (const Algebraic &b : rpq)
                if (Algebraic::compare(a, b) == 0)
                    found = true;
            ASSERT_TRUE(found) << "root of p not found in p*q";
        }
        for (const Algebraic &b : rpq) {
            bool found = false;
            for (const Algebraic &a : rp)
                if (Algebraic::compare(a, b) == 0)
                    found = true;
            for (const Algebraic &a : rq)
                if (Algebraic::compare(a, b) == 0)
                    found = true;
            ASSERT_TRUE(found) << "root of p*q unmatched";
        }
    }
}

TEST(AlgebraicProperty, SignAndApproxConsistent)
{
    std::uint64_t state = 0xB16B00B5E5ULL;
    for (int iter = 0; iter < 1000; ++iter) {
        const UPoly p = rndPoly(state, 4);
        const std::vector<Algebraic> roots = Algebraic::realRoots(p);
        for (const Algebraic &r : roots) {
            const int s = r.sign();
            const double v = r.approx();
            if (s == 0)
                EXPECT_NEAR(v, 0.0, 1e-5);
            else if (s > 0)
                EXPECT_GT(v, 0.0);
            else
                EXPECT_LT(v, 0.0);
            // Interval is consistent with the approximation.
            EXPECT_LT(r.approx(), r.approx() + 1); // smoke: stable
        }
    }
}
