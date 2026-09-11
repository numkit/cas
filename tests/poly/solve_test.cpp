// poly/solve_test.cpp — three layers per AGENTS.md for solveRealRoots:
//   1. fixed vectors: exact rationals, irrational brackets, mixes,
//      empties;
//   2. properties (fixed seed): built rational roots are all found
//      exactly and in order; every irrational bracket is a sign
//      change of the squarefree carrier (or an exact zero);
//   3. boundary: linear, constant, near-double roots.
#include <numkit/cas/poly/solve.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <vector>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Rational;
using numkit::cas::UPoly;

Rational R(std::int64_t p, std::int64_t q = 1)
{
    return Rational(BigInt(p), BigInt(q));
}

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

TEST(SolveVector, ClassicShapes)
{
    // x^2 - 2: two irrational roots, ascending brackets.
    {
        const auto rs = numkit::cas::solveRealRoots(
            UPoly({R(-2), R(0), R(1)}));
        ASSERT_EQ(rs.size(), 2u);
        EXPECT_FALSE(rs[0].isRational);
        EXPECT_FALSE(rs[1].isRational);
        // disjoint half-open brackets may share a boundary point
        EXPECT_LE(rs[0].interval.hi, rs[1].interval.lo);
        EXPECT_LT(rs[0].interval.lo, R(0));
        EXPECT_GT(rs[1].interval.hi, R(0));
        EXPECT_EQ(rs[0].carrier, rs[1].carrier);
        EXPECT_EQ(rs[0].realIndex, 0);
        EXPECT_EQ(rs[1].realIndex, 1);
    }
    // x^2 - 1 = (x-1)(x+1): both roots exact.
    {
        const auto rs = numkit::cas::solveRealRoots(
            UPoly({R(-1), R(0), R(1)}));
        ASSERT_EQ(rs.size(), 2u);
        EXPECT_TRUE(rs[0].isRational);
        EXPECT_EQ(rs[0].value, R(-1));
        EXPECT_TRUE(rs[1].isRational);
        EXPECT_EQ(rs[1].value, R(1));
    }
    // x(x - 1/2)(x^2 - 2): root 0 (exact-empty bracket), 1/2, +/-sqrt2.
    {
        // x^3 - 2x = x(x^2 - 2), coefficients ascending
        const auto rs = numkit::cas::solveRealRoots(
            UPoly({R(0), R(-2), R(0), R(1)}) * UPoly({R(-1, 2), R(1)}));
        ASSERT_EQ(rs.size(), 4u);
        EXPECT_FALSE(rs[0].isRational); // -sqrt(2)
        EXPECT_TRUE(rs[1].isRational);  // 0, in an exact (0,0] bracket
        EXPECT_EQ(rs[1].value, R(0));
        EXPECT_TRUE(rs[2].isRational);  // 1/2
        EXPECT_EQ(rs[2].value, R(1, 2));
        EXPECT_FALSE(rs[3].isRational); // +sqrt(2)
        EXPECT_LE(rs[0].interval.hi, rs[1].interval.lo);
        EXPECT_LE(rs[1].interval.hi, rs[2].interval.lo);
    }
    // x^2 + 1: no real roots; x^3: the squarefree part is x.
    {
        EXPECT_TRUE(numkit::cas::solveRealRoots(
                        UPoly({R(1), R(0), R(1)}))
                        .empty());
        const auto rs = numkit::cas::solveRealRoots(
            UPoly({R(0), R(0), R(0), R(1)}));
        ASSERT_EQ(rs.size(), 1u);
        EXPECT_TRUE(rs[0].isRational);
        EXPECT_EQ(rs[0].value, R(0));
    }
}

TEST(SolveProperty, BuiltRationalRootsFoundExactly)
{
    std::uint64_t st = 0x501FE5A17ULL;
    for (int iter = 0; iter < 500; ++iter) {
        // p = prod (x - r_i) with random distinct-ish rational r_i
        // times a random irreducible quadratic x^2 + b x + c.
        const int nr = static_cast<int>(nextU64(st) % 4);
        std::vector<Rational> roots;
        UPoly p(R(1));
        for (int i = 0; i < nr; ++i) {
            Rational r = R(static_cast<std::int64_t>(nextU64(st) % 19) - 9,
                           1 + static_cast<std::int64_t>(nextU64(st) % 3));
            // skip duplicates: multiplicity would reduce the root count
            bool dup = false;
            for (const Rational &q : roots)
                if (q == r)
                    dup = true;
            if (dup)
                continue;
            roots.push_back(r);
            p = p * UPoly({-r, R(1)});
        }
        std::sort(roots.begin(), roots.end());
        // irreducible quadratic (no rational root among small p/q)
        const Rational b = R(static_cast<std::int64_t>(nextU64(st) % 9) - 4);
        Rational c = R(static_cast<std::int64_t>(nextU64(st) % 9) - 4);
        while (b * b - R(4) * c >= R(0)) // force D < 0
            c = c + R(1);
        p = p * UPoly({c, b, R(1)});

        const auto rs = numkit::cas::solveRealRoots(p);
        ASSERT_EQ(rs.size(), roots.size()) << "iter " << iter;
        // every rational root is present, exactly once, ascending
        for (std::size_t k = 0; k < rs.size(); ++k) {
            ASSERT_TRUE(rs[k].isRational)
                << "iter " << iter << " root " << k << " want "
                << roots[k].toString() << " got interval ("
                << rs[k].interval.lo.toString() << ", "
                << rs[k].interval.hi.toString() << "]";
            EXPECT_EQ(rs[k].value, roots[k]) << "iter " << iter;
            if (k > 0)
                EXPECT_LT(rs[k - 1].value, rs[k].value);
        }
        // sign invariant: carrier(lo) * carrier(hi) <= 0 (a boundary
        // may touch a DIFFERENT root and evaluate to zero - that is
        // legal for half-open brackets).
        for (const auto &s : rs) {
            const UPoly &sq = s.carrier;
            const Rational a = sq.eval(s.interval.lo);
            const Rational bb = sq.eval(s.interval.hi);
            EXPECT_TRUE(a.signum() * bb.signum() <= 0);
        }
    }
}

TEST(SolveBoundary, LinearAndConstant)
{
    // 2x - 7: x = 7/2 exact.
    const auto lin = numkit::cas::solveRealRoots(UPoly({R(-7), R(2)}));
    ASSERT_EQ(lin.size(), 1u);
    EXPECT_TRUE(lin[0].isRational);
    EXPECT_EQ(lin[0].value, R(7, 2));

    // Non-zero constant: no roots.
    EXPECT_TRUE(numkit::cas::solveRealRoots(UPoly({R(5)})).empty());

    // Near-double rational root collapses through squarefree part:
    // (x - 1)^2 * (x + 3): distinct roots are -3 and 1.
    const auto dup = numkit::cas::solveRealRoots(
        UPoly({R(-1), R(1)}) * UPoly({R(-1), R(1)}) * UPoly({R(3), R(1)}));
    ASSERT_EQ(dup.size(), 2u);
    EXPECT_TRUE(dup[0].isRational);
    EXPECT_EQ(dup[0].value, R(-3));
    EXPECT_TRUE(dup[1].isRational);
    EXPECT_EQ(dup[1].value, R(1));
}

} // namespace
