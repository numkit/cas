// num/rational.hpp — canonical exact rational numbers over BigInt.
#pragma once

#include <numkit/cas/num/bigint.hpp>

#include <cstdint>
#include <string>

namespace numkit::cas {

// ============================================================
// Rational — exact rational number in canonical form.
//
// Representation: num_ / den_ with BigInt parts. Invariants:
//   den_ > 0, gcd(|num_|, den_) == 1, zero is 0/1.
// All arithmetic funnels through the (p, q) constructor, which
// enforces the invariants, so every Rational is canonical.
// ============================================================
class Rational
{
public:
    Rational() = default;
    Rational(std::int64_t v);
    Rational(std::uint64_t v);
    Rational(int v) : Rational(static_cast<std::int64_t>(v)) {}

    // q must be non-zero (assert in debug). The constructor moves the sign
    // into the numerator and reduces by the gcd.
    Rational(BigInt p, BigInt q);

    // Strict parse: "<bigint>" or "<signed bigint>/<unsigned bigint>".
    // Denominator zero or malformed input returns false.
    static bool tryParse(Rational &out, const std::string &s);

    bool isZero() const { return num_.isZero(); }
    int signum() const { return num_.signum(); }
    const BigInt &num() const { return num_; }
    const BigInt &den() const { return den_; }

    bool fitsInt64(std::int64_t &out) const; // denominator 1, numerator fits

    // Content hash mixing both parts (for hash-consing; collisions are fine).
    std::uint64_t hashBits() const;

    std::string toString() const; // "p" if den == 1, else "p/q"

    Rational operator-() const;
    Rational abs() const;

    friend Rational operator+(const Rational &a, const Rational &b);
    friend Rational operator-(const Rational &a, const Rational &b);
    friend Rational operator*(const Rational &a, const Rational &b);
    friend Rational operator/(const Rational &a, const Rational &b); // b != 0

    Rational &operator+=(const Rational &o) { return *this = *this + o; }
    Rational &operator-=(const Rational &o) { return *this = *this - o; }
    Rational &operator*=(const Rational &o) { return *this = *this * o; }
    Rational &operator/=(const Rational &o) { return *this = *this / o; }

    friend bool operator==(const Rational &a, const Rational &b);
    friend bool operator!=(const Rational &a, const Rational &b);
    friend bool operator<(const Rational &a, const Rational &b);
    friend bool operator<=(const Rational &a, const Rational &b);
    friend bool operator>(const Rational &a, const Rational &b);
    friend bool operator>=(const Rational &a, const Rational &b);

private:
    // Precondition: den_ != 0. Moves the sign out of the denominator and
    // reduces both parts by gcd(|num_|, den_).
    void canonicalize();

    BigInt num_;
    BigInt den_ = 1;
};

} // namespace numkit::cas
