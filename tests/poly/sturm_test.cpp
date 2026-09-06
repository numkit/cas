#include <numkit/cas/poly/sturm.hpp>

#include <string>
#include <gtest/gtest.h>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Rational;
using numkit::cas::RootInterval;
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

UPoly P(const std::string &csv)
{
    std::vector<Rational> cs;
    std::size_t pos = 0;
    while (pos <= csv.size()) {
        const std::size_t comma = csv.find(',', pos);
        const std::string tok =
            csv.substr(pos, comma == std::string::npos ? std::string::npos
                                                       : comma - pos);
        Rational r;
        if (!Rational::tryParse(r, tok))
            ADD_FAILURE() << "bad coeff: " << tok;
        cs.push_back(r);
        if (comma == std::string::npos)
            break;
        pos = comma + 1;
    }
    return UPoly(std::move(cs));
}

// Approximate decimal value (test values are small and exactly
// representable; used only against the float oracle with 1e-5 slack).
double toD(const Rational &r)
{
    return std::stod(r.num().toString()) / std::stod(r.den().toString());
}

// Python oracle (Durand-Kerner): coefficients, real root count, roots.
struct Case
{
    const char *poly;
    int count;
    std::vector<double> roots;
};

const Case kCases[] = {
    {"-1,0,1", 2, {-1.000000000, 1.000000000}},
    {"1,0,1", 0, {}},
    {"0,-1,0,1", 3, {-1.000000000, 0.000000000, 1.000000000}},
    {"1,0,0,0,1", 0, {}},
    {"-6,11,-6,1", 3, {1.000000000, 2.000000000, 3.000000000}},
    {"0,0,0,1", 1, {-0.000000000}},
    {"-3,1", 1, {3.000000000}},
    {"2,0,1", 0, {}},
    {"3,1,5,2,1", 0, {}},
    {"-4,-4", 1, {-1.000000000}},
    {"-9,-6", 1, {-1.500000000}},
    {"3,3/2,5/2,-3/2,-2,0,6", 0, {}},
    {"-9,6,5,9,-3", 2, {0.699244433, 3.559554066}},
    {"6,8,6,-3,-2,-2", 1, {1.440340653}},
    {"0,6", 1, {0.000000000}},
    {"-5,-1", 1, {-5.000000000}},
    {"7,6,-4", 2, {-0.770690633, 2.270690633}},
    {"1,3,-4,-3,-1,3", 3, {-0.258739756, 0.775799152, 1.314010321}},
};

} // namespace

TEST(SturmFixed, OracleVectors)
{
    for (const Case &c : kCases) {
        const UPoly p = P(c.poly);
        const std::vector<RootInterval> roots = numkit::cas::isolateRealRoots(p);
        ASSERT_EQ(roots.size(), static_cast<std::size_t>(c.count)) << c.poly;
        ASSERT_EQ(roots.size(), c.roots.size());
        for (std::size_t i = 0; i < roots.size(); ++i) {
            const RootInterval iv = numkit::cas::refineRoot(
                p.squarefreePart(), roots[i],
                Rational(std::int64_t{1}, BigInt(1000000)));
            EXPECT_LE(toD(iv.lo), c.roots[i] + 1e-5) << c.poly;
            EXPECT_GE(toD(iv.hi), c.roots[i] - 1e-5) << c.poly;
        }
    }
}

TEST(SturmFixed, KnownBounds)
{
    // sqrt(2) is the positive root of x^2 - 2.
    const UPoly q = P("-2,0,1");
    const std::vector<RootInterval> roots = numkit::cas::isolateRealRoots(q);
    ASSERT_EQ(roots.size(), 2u);
    const RootInterval r2 = numkit::cas::refineRoot(
        q, roots[1], Rational(std::int64_t{1}, BigInt(1000000)));
    const double mid = 0.5 * (toD(r2.lo) + toD(r2.hi));
    EXPECT_NEAR(mid, 1.414213562, 1e-5);

    // All roots within the Cauchy bound.
    const Rational B = numkit::cas::cauchyRootBound(q);
    for (const RootInterval &iv : roots) {
        EXPECT_LE(iv.lo.abs(), B);
        EXPECT_LE(iv.hi.abs(), B);
    }
}

TEST(SturmProperty, IsolationInvariants)
{
    std::uint64_t state = 0x5714571457145714ULL;
    for (int iter = 0; iter < 3000; ++iter) {
        const int deg = 1 + static_cast<int>(nextU64(state) % 6);
        std::vector<Rational> cs;
        for (int i = 0; i < deg; ++i)
            cs.push_back(rr(state, 6));
        cs.push_back(rr(state, 5).isZero() ? Rational(std::int64_t{1}) : rr(state, 5));
        const UPoly p(cs);

        const UPoly psf = p.squarefreePart();
        if (p.isConst())
            continue; // generator can produce constants (trimmed zeros)
        const std::vector<RootInterval> roots = numkit::cas::isolateRealRoots(p);
        const std::vector<UPoly> sturm = numkit::cas::sturmSequence(psf);

        // Pairwise disjoint interiors, ordered; endpoints may be exact
        // roots shared with neighbours.
        for (std::size_t i = 0; i < roots.size(); ++i) {
            if (roots[i].exact()) {
                EXPECT_TRUE(psf.eval(roots[i].lo).isZero());
            } else if (!psf.eval(roots[i].lo).isZero() && !psf.eval(roots[i].hi).isZero()) {
                // Sign change: one simple root of the squarefree part.
                EXPECT_TRUE((psf.eval(roots[i].lo) * psf.eval(roots[i].hi)).signum() < 0);
                EXPECT_EQ(numkit::cas::countRealRoots(sturm, roots[i].lo, roots[i].hi), 1u);
            }
            if (i + 1 < roots.size())
                EXPECT_LE(roots[i].hi, roots[i + 1].lo);
        }
        // Count outside all intervals is zero (within the Cauchy bound).
        const Rational B = numkit::cas::cauchyRootBound(p);
        EXPECT_EQ(numkit::cas::countRealRoots(sturm, -B, B), roots.size());

        // Refinement keeps the root and shrinks the interval.
        for (const RootInterval &iv : roots) {
            const RootInterval fine = numkit::cas::refineRoot(
                psf, iv, Rational(std::int64_t{1}, BigInt(1 << 20)));
            if (fine.exact()) {
                EXPECT_TRUE(psf.eval(fine.lo).isZero());
            } else {
                EXPECT_LE(fine.hi - fine.lo, Rational(std::int64_t{1}, BigInt(1 << 20)));
                if (!psf.eval(fine.lo).isZero() && !psf.eval(fine.hi).isZero())
                    EXPECT_TRUE((psf.eval(fine.lo) * psf.eval(fine.hi)).signum() < 0);
            }
        }
    }
}

TEST(SturmProperty, KnownRationalRootsContained)
{
    std::uint64_t state = 0x244466668888ULL + 1;
    for (int iter = 0; iter < 2000; ++iter) {
        // Product of known rational roots: every root must be isolated.
        const int k = 1 + static_cast<int>(nextU64(state) % 4);
        std::vector<Rational> wanted;
        UPoly p(Rational(std::int64_t{1}));
        for (int i = 0; i < k; ++i) {
            Rational r = rr(state, 8);
            if (r.isZero())
                r = Rational(std::int64_t{1});
            bool dup = false;
            for (const Rational &w : wanted)
                if (w == r)
                    dup = true;
            if (dup)
                continue;
            wanted.push_back(r);
            p = p * UPoly(std::vector<Rational>{Rational(-r), Rational(std::int64_t{1})});
        }
        const std::vector<RootInterval> roots = numkit::cas::isolateRealRoots(p);
        ASSERT_EQ(roots.size(), wanted.size());
        for (const Rational &w : wanted) {
            bool found = false;
            for (const RootInterval &iv : roots)
                if (iv.exact() ? iv.lo == w : (iv.lo < w && w < iv.hi))
                    found = true;
            EXPECT_TRUE(found) << "root " << w.toString() << " of " << p.toString();
        }
    }
}
