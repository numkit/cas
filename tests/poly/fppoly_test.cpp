#include <numkit/cas/poly/fppoly.hpp>

#include <gtest/gtest.h>

namespace {

using numkit::cas::BigInt;
using numkit::cas::FpPoly;

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

FpPoly P(std::uint64_t p, const std::vector<std::uint64_t> &cs)
{
    return FpPoly(p, cs);
}

// Full independent correctness proof of a factorization:
// (a) the product of the factors reconstructs the squarefree input;
// (b) every factor is monic and passes the Fermat irreducibility
//     criterion (which does not use factor()).
void verifyFactorization(const FpPoly &f, const std::vector<FpPoly> &factors)
{
    FpPoly prod = FpPoly::constant(f.p(), 1);
    for (const FpPoly &g : factors) {
        ASSERT_TRUE(g.isIrreducible()) << "reducible factor in output";
        ASSERT_EQ(g.lc(), 1u);
        prod = prod * g;
    }
    const FpPoly sf = [&] {
        FpPoly s = f;
        const FpPoly g = FpPoly::gcd(f, f.derivative());
        if (!g.isOne() && !g.isZero()) {
            FpPoly q, r;
            FpPoly::divMod(f, g, q, r);
            s = q;
        }
        // factor() output is monic: compare against the monic associate.
        FpPoly q, r;
        FpPoly::divMod(s, FpPoly::constant(f.p(), s.lc()), q, r);
        return q;
    }();
    ASSERT_EQ(prod, sf);
}

} // namespace

TEST(FpPolyBasics, Arithmetic)
{
    const std::uint64_t p = 7;
    // (x + 3)(x + 5) = x^2 + x + 1 (mod 7): 3+5=8=1, 15=1
    const FpPoly a = P(p, {3, 1});
    const FpPoly b = P(p, {5, 1});
    EXPECT_EQ(a * b, P(p, {1, 1, 1}));
    EXPECT_EQ(a + b, P(p, {1, 2}));
    EXPECT_EQ(a - a, FpPoly());
    // x^2 + 1 = (x + 2)(x + 5) mod 7: 2+5=0, 10=3? no: 2*5=10=3.
    // Correct classic: x^2+1 = (x+3)(x+4)? 3+4=0, 12=5 no. Roots of
    // x^2+1 mod 7: x^2=6 -> x=±? 1,4,2,2,4,1 -> no root; irreducible.
    EXPECT_TRUE(P(p, {1, 0, 1}).isIrreducible());
    EXPECT_FALSE(P(p, {1, 1, 1}).isIrreducible());
}

TEST(FpPolyBasics, DivisionAndGcd)
{
    const std::uint64_t p = 101;
    FpPoly q, r;
    FpPoly::divMod(P(p, {1, 2, 3}), P(p, {5, 1}), q, r);
    EXPECT_EQ(q * P(p, {5, 1}) + r, P(p, {1, 2, 3}));
    EXPECT_TRUE(r.isZero() || r.deg() < 1);
    // gcd(2+x, 4+2x) = 1 + x/... monic gcd of (x+2) and 2(x+2) is (x+2).
    EXPECT_EQ(FpPoly::gcd(P(p, {2, 1}), P(p, {4, 2})), P(p, {2, 1}));
}

TEST(FpPolyFixed, ExtGcdIdentity)
{
    std::uint64_t state = 0xE7C0FFEE42ULL;
    for (int iter = 0; iter < 500; ++iter) {
        const std::uint64_t p = 7;
        const int da = 1 + static_cast<int>(nextU64(state) % 4);
        const int db = 1 + static_cast<int>(nextU64(state) % 3);
        std::vector<std::uint64_t> ca, cb;
        for (int i = 0; i < da; ++i) ca.push_back(nextU64(state) % p);
        ca.push_back(1 + nextU64(state) % (p - 1));
        for (int i = 0; i < db; ++i) cb.push_back(nextU64(state) % p);
        cb.push_back(1 + nextU64(state) % (p - 1));
        const FpPoly a(p, ca), b(p, cb);
        if (FpPoly::gcd(a, b).deg() != 0)
            continue; // need coprime
        FpPoly s, t;
        FpPoly::extGcd(a, b, s, t);
        ASSERT_TRUE((s * a + t * b).isOne()) << "extGcd identity broken";
    }
}

TEST(FpPolyFixed, ClassicFactorizations)
{
    // x^5 - 1 = (x-1)(x^4+x^3+x^2+x+1) mod 3; the quartic is
    // irreducible mod 3 (order of 3 mod 5 is 4).
    const std::vector<FpPoly> f1 = FpPoly::factor(P(3, {2, 0, 0, 0, 0, 1}));
    ASSERT_EQ(f1.size(), 2u);
    EXPECT_EQ(f1[0].deg(), 1);
    EXPECT_EQ(f1[1].deg(), 4);
    verifyFactorization(P(3, {2, 0, 0, 0, 0, 1}), f1);

    // x^7 - x mod 7 splits completely into 7 linears.
    std::vector<std::uint64_t> cs8(8, 0);
    cs8[1] = 6; // -x
    cs8[7] = 1;
    const std::vector<FpPoly> f2 = FpPoly::factor(P(7, cs8));
    ASSERT_EQ(f2.size(), 7u);
    for (const FpPoly &g : f2)
        EXPECT_EQ(g.deg(), 1);
    verifyFactorization(P(7, cs8), f2);

    // x^4 + x + 1 is irreducible mod 2... use p=5: x^4+2 over 5 is a
    // classic irreducible (2 is not a fourth power and -1 check);
    // simpler verified classic: x^3 + x + 1 mod 2 -> use p=3: no roots
    // in F_3 (1+1+1=0? f(1)=3=0 -> has root). Use x^3+2x+1 mod 5:
    // f(0)=1 f(1)=4 f(2)=8+4+1=13=3 f(3)=27+6+1=34=4 f(4)=64+8+1=73=3
    // -> no roots -> irreducible cubic.
    EXPECT_TRUE(P(5, {1, 2, 0, 1}).isIrreducible());
    const std::vector<FpPoly> f3 = FpPoly::factor(P(5, {1, 2, 0, 1}));
    ASSERT_EQ(f3.size(), 1u);
    verifyFactorization(P(5, {1, 2, 0, 1}), f3);
}

TEST(FpPolyProperty, RandomFactorizations)
{
    std::uint64_t state = 0xFACC1337C0DEULL;
    for (int iter = 0; iter < 500; ++iter) {
        const std::uint64_t p = (iter % 2 == 0) ? 101 : 7;
        const int deg = 2 + static_cast<int>(nextU64(state) % 6);
        std::vector<std::uint64_t> cs;
        for (int i = 0; i < deg; ++i)
            cs.push_back(nextU64(state) % p);
        cs.push_back(1 + nextU64(state) % (p - 1)); // monic, nonzero lc
        const FpPoly f(p, cs);
        if (f.deg() < 1)
            continue;
        // Skip non-squarefree inputs occasionally included on purpose:
        // factor() handles them (squarefree part); verification uses
        // the squarefree part too.
        const std::vector<FpPoly> factors = FpPoly::factor(f);
        verifyFactorization(f, factors);

        // Determinism: same input, same output.
        const std::vector<FpPoly> factors2 = FpPoly::factor(f);
        ASSERT_EQ(factors.size(), factors2.size());
        for (std::size_t i = 0; i < factors.size(); ++i)
            ASSERT_EQ(factors[i], factors2[i]);
    }
}

TEST(FpPolyProperty, BuiltFromKnownIrreducibles)
{
    // Product of independently-built irreducibles factors back into
    // exactly those factors (up to ordering, which is deterministic).
    std::uint64_t state = 0x123499887766ULL;
    int checked = 0;
    while (checked < 60) {
        const std::uint64_t p = 101;
        const int deg = 1 + static_cast<int>(nextU64(state) % 4);
        std::vector<std::uint64_t> cs;
        for (int i = 0; i < deg; ++i)
            cs.push_back(nextU64(state) % p);
        cs.push_back(1);
        const FpPoly f(p, cs);
        if (f.deg() < 1 || !f.isIrreducible())
            continue;
        const FpPoly h = P(p, {static_cast<std::uint64_t>(1 + nextU64(state) % 100), 1});
        const FpPoly prod = f * h;
        const std::vector<FpPoly> factors = FpPoly::factor(prod);
        verifyFactorization(prod, factors);
        // The multiset contains f and h.
        bool foundF = false, foundH = false;
        for (const FpPoly &g : factors) {
            if (g == f)
                foundF = true;
            if (g == h)
                foundH = true;
        }
        ASSERT_TRUE(foundF && foundH) << "known factor lost";
        ++checked;
    }
}
