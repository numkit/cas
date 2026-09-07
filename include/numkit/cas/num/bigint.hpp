// num/bigint.hpp — arbitrary-precision integer, exact arithmetic layer.
#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace numkit::cas {

// ============================================================
// BigInt — signed arbitrary-precision integer.
//
// Representation: signed magnitude, little-endian base-2^64 limbs.
// Invariants: no trailing zero limbs; zero is the empty limb vector
// with negative_ == false (no negative zero).
//
// Division/modulo follow C truncated semantics:
//   a == (a/b)*b + (a%b), |a%b| < |b|, sign(a%b) == sign(a) or zero.
// Division by zero is a caller contract violation (assert in debug).
// ============================================================
class BigInt
{
public:
    BigInt() = default;
    BigInt(std::int64_t v);
    BigInt(std::uint64_t v); // non-negative
    BigInt(int v) : BigInt(static_cast<std::int64_t>(v)) {}

    // Strict decimal parse: optional sign, one or more digits, no whitespace.
    static bool tryParse(BigInt &out, const std::string &s);

    bool isZero() const { return limbs_.empty(); }
    int signum() const;
    bool isNegative() const { return negative_; }
    std::size_t bitLength() const;

    // Undefined on zero magnitude access to the low limb.
    std::uint64_t lowLimb() const { return limbs_.empty() ? 0 : limbs_[0]; }

    bool fitsInt64(std::int64_t &out) const;
    bool fitsUint64(std::uint64_t &out) const;

    std::string toString() const;

    BigInt abs() const;
    BigInt operator-() const;

    friend BigInt operator+(const BigInt &a, const BigInt &b);
    friend BigInt operator-(const BigInt &a, const BigInt &b);
    friend BigInt operator*(const BigInt &a, const BigInt &b);
    friend BigInt operator/(const BigInt &a, const BigInt &b);
    friend BigInt operator%(const BigInt &a, const BigInt &b);

    BigInt &operator+=(const BigInt &o) { return *this = *this + o; }
    BigInt &operator-=(const BigInt &o) { return *this = *this - o; }
    BigInt &operator*=(const BigInt &o) { return *this = *this * o; }

    friend bool operator==(const BigInt &a, const BigInt &b);
    friend bool operator!=(const BigInt &a, const BigInt &b);
    friend bool operator<(const BigInt &a, const BigInt &b);
    friend bool operator<=(const BigInt &a, const BigInt &b);
    friend bool operator>(const BigInt &a, const BigInt &b);
    friend bool operator>=(const BigInt &a, const BigInt &b);

    BigInt operator<<(std::size_t bits) const;
    BigInt operator>>(std::size_t bits) const; // floor semantics for negatives

    static void divMod(const BigInt &a, const BigInt &b, BigInt &q, BigInt &r);
    static BigInt gcd(const BigInt &a, const BigInt &b); // non-negative result
    static BigInt powUInt(const BigInt &base, std::uint64_t exp); // 0^0 == 1
    static BigInt lcm(const BigInt &a, const BigInt &b);          // non-negative

    // Primality by Miller-Rabin. Deterministic for n < 2^64 (the
    // fixed base set {2,...,37} has no strong pseudoprime there);
    // above 2^64 the same bases plus a fixed pseudo-random stream
    // make it probabilistic with error < 4^-50 — and a missed factor
    // can only ever drop divisors from enumeration, never invent
    // them, so callers stay correct (worst case: less factoring).
    static bool isPrime(const BigInt &n);

    // Canonical factorization of n >= 1 into (prime, exponent) pairs
    // with primes ascending. Deterministic (Pollard-Brent rho with a
    // fixed c-sequence).
    static std::vector<std::pair<BigInt, int>> factorize(const BigInt &n);

    // Exact integer square root (false for negatives and non-squares).
    bool sqrtExact(BigInt &out) const;

    // Order-insensitive content hash for hash-consing (collisions are fine).
    std::uint64_t hashBits() const;

private:
    void normalize();
    int compareMagnitude(const BigInt &o) const;
    static BigInt addMagnitude(const BigInt &a, const BigInt &b);
    static BigInt subMagnitude(const BigInt &a, const BigInt &b); // |a| >= |b|

    std::vector<std::uint64_t> limbs_;
    bool negative_ = false;
};

} // namespace numkit::cas
