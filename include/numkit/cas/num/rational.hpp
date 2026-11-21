// num/rational.hpp — canonical exact rational numbers over BigInt.
// Thin adapter delegating to keel::bignum::Rational (<keel/rational.h>).
#pragma once

#include <keel/core.h>
#include <keel/rational.h>
#include <keel/string.h>
#include <numkit/cas/num/bigint.hpp>

namespace numkit::cas {

class Rational {
public:
    Rational() noexcept = default;
    explicit Rational(keel::bignum::Rational raw) noexcept : v_(keel::move(raw)) {}
    Rational(keel::i64 v) noexcept : v_(v) {}
    Rational(keel::u64 v) noexcept : v_(v) {}
    Rational(int v) noexcept : v_(keel::as<keel::i64>(v)) {}

    Rational(BigInt p, BigInt q) : v_(keel::move(p.raw()), keel::move(q.raw())) {}

    const keel::bignum::Rational &raw() const noexcept { return v_; }
    keel::bignum::Rational &raw() noexcept { return v_; }

    static bool tryParse(Rational &out, keel::StringRef s)
    {
        return keel::bignum::Rational::try_parse(out.v_, s);
    }

    static Rational fromDoubleBits(keel::f64 v)
    {
        return Rational(keel::bignum::Rational::from_f64_bits(v));
    }

    keel::f64 toDouble() const { return v_.to_f64(); }

    bool isZero() const noexcept { return v_.is_zero(); }
    int signum() const noexcept { return keel::as<int>(v_.signum()); }
    BigInt num() const { return BigInt(v_.num()); }
    BigInt den() const { return BigInt(v_.den()); }

    bool fitsInt64(keel::i64 &out) const noexcept { return v_.fits_i64(out); }
    keel::u64 hashBits() const noexcept { return v_.hash_bits(); }

    static Rational powUInt(const Rational &base, keel::u64 exp)
    {
        return Rational(keel::bignum::Rational::pow_u64(base.v_, exp));
    }

    keel::String toString() const { return v_.to_string(); }

    Rational operator-() const { return Rational(-v_); }
    Rational abs() const { return Rational(v_.abs()); }

    friend Rational operator+(const Rational &a, const Rational &b) { return Rational(a.v_ + b.v_); }
    friend Rational operator-(const Rational &a, const Rational &b) { return Rational(a.v_ - b.v_); }
    friend Rational operator*(const Rational &a, const Rational &b) { return Rational(a.v_ * b.v_); }
    friend Rational operator/(const Rational &a, const Rational &b) { return Rational(a.v_ / b.v_); }

    Rational &operator+=(const Rational &o) { v_ += o.v_; return *this; }
    Rational &operator-=(const Rational &o) { v_ -= o.v_; return *this; }
    Rational &operator*=(const Rational &o) { v_ *= o.v_; return *this; }
    Rational &operator/=(const Rational &o) { v_ /= o.v_; return *this; }

    friend bool operator==(const Rational &a, const Rational &b) noexcept { return a.v_ == b.v_; }
    friend bool operator!=(const Rational &a, const Rational &b) noexcept { return a.v_ != b.v_; }
    friend bool operator<(const Rational &a, const Rational &b) { return a.v_ < b.v_; }
    friend bool operator<=(const Rational &a, const Rational &b) { return a.v_ <= b.v_; }
    friend bool operator>(const Rational &a, const Rational &b) { return a.v_ > b.v_; }
    friend bool operator>=(const Rational &a, const Rational &b) { return a.v_ >= b.v_; }

private:
    keel::bignum::Rational v_;
};

} // namespace numkit::cas
