// Shared helpers for num-layer tests: gtest printers (ADL) and
// seeded PRNG generators for property tests.
#pragma once

#include <numkit/cas/num/bigint.hpp>
#include <numkit/cas/num/rational.hpp>

#include <cstdint>
#include <ostream>
#include <string>

namespace numkit::cas {

inline void PrintTo(const BigInt &v, std::ostream *os)
{
    *os << v.toString();
}

inline void PrintTo(const Rational &v, std::ostream *os)
{
    *os << v.toString();
}

} // namespace numkit::cas

namespace cas_test {

using numkit::cas::BigInt;
using numkit::cas::Rational;

inline std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

inline BigInt parse(const std::string &s)
{
    BigInt v;
    if (!BigInt::tryParse(v, s))
        ADD_FAILURE() << "BigInt::tryParse failed on: " << s;
    return v;
}

inline Rational parseR(const std::string &s)
{
    Rational v;
    if (!Rational::tryParse(v, s))
        ADD_FAILURE() << "Rational::tryParse failed on: " << s;
    return v;
}

inline BigInt randomBig(std::uint64_t &state, int maxLimbs)
{
    static const char *nasty[] = {
        "0", "1", "-1", "2", "-2", "18446744073709551615",
        "18446744073709551616", "9223372036854775807",
        "-9223372036854775808", "999999999999999999",
        "1000000000000000000", "-1000000000000000000",
    };
    if (nextU64(state) % 8 == 0)
        return parse(nasty[nextU64(state) % 12]);

    const int limbs = static_cast<int>(nextU64(state) % (maxLimbs + 1));
    BigInt out;
    for (int i = 0; i < limbs; ++i) {
        const std::uint64_t limb = nextU64(state) | (i + 1 == limbs ? 1 : 0);
        out = (out << 64) + BigInt(limb);
    }
    if (!out.isZero() && nextU64(state) & 1)
        out = -out;
    return out;
}

inline Rational randomRational(std::uint64_t &state, int maxLimbs)
{
    BigInt den = randomBig(state, maxLimbs).abs();
    if (den.isZero())
        den = BigInt(1);
    return Rational(randomBig(state, maxLimbs), den);
}

} // namespace cas_test
