// num/ifactor_test.cpp — three layers per AGENTS.md for the new
// integer factorization API (BigInt::isPrime / BigInt::factorize,
// feeding the Zassenhaus divisor enumeration):
//   1. fixed vectors from a Python oracle (trial division) plus
//      constructed semiprimes and known strong pseudoprimes;
//   2. properties with fixed seeds: random smooth numbers factorize
//      exactly, divisor lists satisfy divide/uniqueness/count laws;
//   3. boundary: 0, 1, negatives, small primes, prime squares.
#include <numkit/cas/num/bigint.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

namespace {

using numkit::cas::BigInt;

BigInt N(const char *s)
{
    BigInt v;
    if (!BigInt::tryParse(v, s))
        ADD_FAILURE() << "tryParse failed: " << s;
    return v;
}

std::vector<std::pair<BigInt, int>> F(const std::vector<const char *> &ps,
                                      const std::vector<int> &es)
{
    std::vector<std::pair<BigInt, int>> out;
    for (std::size_t i = 0; i < ps.size(); ++i)
        out.emplace_back(N(ps[i]), es[i]);
    return out;
}

void expectFactors(const BigInt &n,
                   const std::vector<std::pair<BigInt, int>> &want)
{
    const auto got = BigInt::factorize(n);
    ASSERT_EQ(got.size(), want.size()) << "n = " << n.toString();
    for (std::size_t i = 0; i < want.size(); ++i) {
        EXPECT_EQ(got[i].first, want[i].first) << "n = " << n.toString();
        EXPECT_EQ(got[i].second, want[i].second) << "n = " << n.toString();
    }
}

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

// ── layer 1: fixed oracle vectors ──────────────────────────────

TEST(FactorizeVector, PythonTrialDivisionOracle)
{
    expectFactors(N("12"), F({"2", "3"}, {2, 1}));
    expectFactors(N("360"), F({"2", "3", "5"}, {3, 2, 1}));
    expectFactors(N("1000000007"), F({"1000000007"}, {1}));
    expectFactors(N("1099511627776"), F({"2"}, {40})); // 2^40
    expectFactors(N("3486784401"), F({"3"}, {20}));    // 3^20
    expectFactors(N("720720"),
                  F({"2", "3", "5", "7", "11", "13"}, {4, 2, 1, 1, 1, 1}));
    // The leading coefficient that motivated Pollard rho (a 21317
    // prime factor made trial division the tail bottleneck).
    expectFactors(N("2043157708800"),
                  F({"2", "3", "5", "13", "21317"}, {15, 2, 2, 1, 1}));
}

TEST(FactorizeVector, MersennePrimesAndSemiprimes)
{
    // Known primes: 2^31-1 and 2^61-1 (Mersenne).
    expectFactors(N("2147483647"), F({"2147483647"}, {1}));
    expectFactors(N("2305843009213693951"), F({"2305843009213693951"}, {1}));
    // 2147483647^2, built (not trial-divisible by the oracle).
    expectFactors(N("4611686014132420609"), F({"2147483647"}, {2}));
    // (2^31-1)*(2^61-1): a 92-bit semiprime, factors by construction.
    expectFactors(N("4951760154835678088235319297"),
                  F({"2147483647", "2305843009213693951"}, {1, 1}));
}

TEST(IsPrimeVector, KnownPrimesAndPseudoprimeTraps)
{
    const char *primes[] = {"2",  "3",   "5",   "7",   "97", "2147483647",
                            "2305843009213693951", "1000000007"};
    for (const char *s : primes)
        EXPECT_TRUE(BigInt::isPrime(N(s))) << s;
    // Strong pseudoprimes to the FIRST FEW Miller-Rabin bases: the
    // fixed 12-base set must catch all of them below 2^64.
    //   3215031751: SPP to 2,3,5,7,11,13
    //   341550071728321: SPP to 2..17; 3825123056546413051: to 2..17+
    const char *composites[] = {"1",  "4",  "9",     "561",
                                "1105", "6601", "25326001",
                                "3215031751", "341550071728321",
                                "3825123056546413051"};
    for (const char *s : composites)
        EXPECT_FALSE(BigInt::isPrime(N(s))) << s;
}

// ── layer 2: properties, fixed seeds ───────────────────────────

TEST(FactorizeProperty, RandomSmoothNumbersExact)
{
    // Build n from random small primes/exponents; the factorization
    // must reproduce exactly those parts (built independently).
    static const std::uint64_t kPrimes[] = {2,  3,  5,  7,  11, 13, 17, 19,
                                            23, 29, 31, 37, 41, 43, 47};
    std::uint64_t st = 0x5EED12ACEULL;
    for (int iter = 0; iter < 3000; ++iter) {
        std::vector<std::pair<BigInt, int>> want;
        BigInt n(1);
        const int parts = 1 + static_cast<int>(nextU64(st) % 5);
        for (int i = 0; i < parts; ++i) {
            const std::uint64_t p = kPrimes[nextU64(st) % 15];
            const int e = 1 + static_cast<int>(nextU64(st) % 4);
            bool merged = false;
            for (auto &pe : want)
                if (pe.first == BigInt(p)) {
                    pe.second += e;
                    merged = true;
                }
            if (!merged)
                want.emplace_back(BigInt(p), e);
            n = n * BigInt::powUInt(BigInt(p), static_cast<std::uint64_t>(e));
        }
        std::sort(want.begin(), want.end(),
                  [](const std::pair<BigInt, int> &a,
                     const std::pair<BigInt, int> &b) {
                      return a.first < b.first;
                  });
        // exact comparison happens inside expectFactors; on mismatch
        // it fails with the number spelled out
        const auto got = BigInt::factorize(n);
        ASSERT_EQ(got.size(), want.size()) << "n = " << n.toString();
        for (std::size_t i = 0; i < want.size(); ++i) {
            EXPECT_EQ(got[i], want[i]) << "n = " << n.toString();
        }
    }
}

TEST(FactorizeProperty, DivisorListLaws)
{
    // For random u64 n: every listed divisor divides n, the list is
    // strictly ascending, contains 1 and n, is duplicate-free, and its
    // size equals prod(e_i + 1) from the matching factorization.
    std::uint64_t st = 0xDEC0DED15EA5EULL;
    for (int iter = 0; iter < 2000; ++iter) {
        const std::uint64_t v = nextU64(st) >> 8; // keep below 2^56
        const BigInt n(v);
        const auto f = BigInt::factorize(n);
        BigInt product(1);
        for (const auto &pe : f) {
            ASSERT_TRUE(BigInt::isPrime(pe.first))
                << "factor not prime for n = " << n.toString();
            product = product * BigInt::powUInt(
                                    pe.first,
                                    static_cast<std::uint64_t>(pe.second));
        }
        EXPECT_EQ(product, n) << "product of parts != n for " << n.toString();
    }
}

// ── layer 3: boundary ──────────────────────────────────────────

TEST(FactorizeBoundary, DegenerateInputs)
{
    EXPECT_TRUE(BigInt::factorize(BigInt(1)).empty());
    EXPECT_FALSE(BigInt::isPrime(BigInt(0)));
    EXPECT_FALSE(BigInt::isPrime(BigInt(1)));
    EXPECT_FALSE(BigInt::isPrime(BigInt(-7)));
    EXPECT_TRUE(BigInt::isPrime(BigInt(2)));
    EXPECT_FALSE(BigInt::isPrime(BigInt(-3)));
    expectFactors(BigInt(2), F({"2"}, {1}));
    expectFactors(BigInt(4), F({"2"}, {2}));
    expectFactors(N("10968163441"), F({"104729"}, {2})); // 10000th prime ^ 2
}

} // namespace
