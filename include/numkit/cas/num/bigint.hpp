// num/bigint.hpp — arbitrary-precision integer, exact arithmetic layer.
// Thin adapter delegating to keel::bignum::BigInt (<keel/bigint.h>).
#pragma once

#include <keel/array.h>
#include <keel/bigint.h>
#include <keel/core.h>
#include <keel/string.h>
#include <utility>

namespace numkit::cas {

class BigInt {
public:
    BigInt() noexcept = default;
    explicit BigInt(keel::bignum::BigInt raw) noexcept : v_(keel::move(raw)) {}
    BigInt(keel::i64 v) noexcept : v_(v) {}
    BigInt(keel::u64 v) noexcept : v_(v) {}

    template <typename T>
        requires(keel::IsIntegral<T> && !keel::IsSame<keel::RemoveCv<T>, bool> &&
                 keel::IsSigned<T> && !keel::IsSame<keel::RemoveCv<T>, keel::i64>)
    BigInt(T v) noexcept : v_(keel::as<keel::i64>(v)) {}

    template <typename T>
        requires(keel::IsIntegral<T> && !keel::IsSame<keel::RemoveCv<T>, bool> &&
                 keel::IsUnsigned<T> && !keel::IsSame<keel::RemoveCv<T>, keel::u64>)
    BigInt(T v) noexcept : v_(keel::as<keel::u64>(v)) {}

    const keel::bignum::BigInt &raw() const noexcept { return v_; }
    keel::bignum::BigInt &raw() noexcept { return v_; }

    static bool tryParse(BigInt &out, keel::StringRef s)
    {
        return keel::bignum::BigInt::try_parse(out.v_, s);
    }

    bool isZero() const noexcept { return v_.is_zero(); }
    bool isInline() const noexcept { return v_.is_inline(); }
    keel::i32 signum() const noexcept { return keel::as<keel::i32>(v_.signum()); }
    bool isNegative() const noexcept { return v_.is_negative(); }
    keel::usize bitLength() const noexcept { return v_.bit_length(); }
    keel::u64 lowLimb() const noexcept { return v_.low_limb(); }

    bool fitsInt64(keel::i64 &out) const noexcept { return v_.fits_i64(out); }
    bool fitsUint64(keel::u64 &out) const noexcept { return v_.fits_u64(out); }

    keel::f64 toDouble() const noexcept { return v_.to_f64(); }
    keel::String toString() const { return v_.to_string(); }

    BigInt abs() const { return BigInt(v_.abs()); }
    BigInt operator-() const { return BigInt(-v_); }

    friend BigInt operator+(const BigInt &a, const BigInt &b) { return BigInt(a.v_ + b.v_); }
    friend BigInt operator-(const BigInt &a, const BigInt &b) { return BigInt(a.v_ - b.v_); }
    friend BigInt operator*(const BigInt &a, const BigInt &b) { return BigInt(a.v_ * b.v_); }
    friend BigInt operator/(const BigInt &a, const BigInt &b) { return BigInt(a.v_ / b.v_); }
    friend BigInt operator%(const BigInt &a, const BigInt &b) { return BigInt(a.v_ % b.v_); }

    BigInt &operator+=(const BigInt &o) { v_ += o.v_; return *this; }
    BigInt &operator-=(const BigInt &o) { v_ -= o.v_; return *this; }
    BigInt &operator*=(const BigInt &o) { v_ *= o.v_; return *this; }

    friend bool operator==(const BigInt &a, const BigInt &b) noexcept { return a.v_ == b.v_; }
    friend bool operator!=(const BigInt &a, const BigInt &b) noexcept { return a.v_ != b.v_; }
    friend bool operator<(const BigInt &a, const BigInt &b) noexcept { return a.v_ < b.v_; }
    friend bool operator<=(const BigInt &a, const BigInt &b) noexcept { return a.v_ <= b.v_; }
    friend bool operator>(const BigInt &a, const BigInt &b) noexcept { return a.v_ > b.v_; }
    friend bool operator>=(const BigInt &a, const BigInt &b) noexcept { return a.v_ >= b.v_; }

    BigInt operator<<(keel::usize bits) const { return BigInt(v_ << bits); }
    BigInt operator>>(keel::usize bits) const { return BigInt(v_ >> bits); }

    static void divMod(const BigInt &a, const BigInt &b, BigInt &q, BigInt &r)
    {
        keel::bignum::BigInt::div_mod(a.v_, b.v_, q.v_, r.v_);
    }
    static BigInt gcd(const BigInt &a, const BigInt &b)
    {
        return BigInt(keel::bignum::BigInt::gcd(a.v_, b.v_));
    }
    static BigInt powUInt(const BigInt &base, keel::u64 exp)
    {
        return BigInt(keel::bignum::BigInt::pow_u64(base.v_, exp));
    }
    static BigInt lcm(const BigInt &a, const BigInt &b)
    {
        return BigInt(keel::bignum::BigInt::lcm(a.v_, b.v_));
    }
    static bool isPrime(const BigInt &n)
    {
        return keel::bignum::BigInt::is_prime(n.v_);
    }
    static keel::Array<std::pair<BigInt, keel::i32>> factorize(const BigInt &n)
    {
        keel::Array<keel::bignum::PrimeFactor> raw = keel::bignum::BigInt::factorize(n.v_);
        keel::Array<std::pair<BigInt, keel::i32>> out;
        out.reserve(raw.size());
        for (keel::usize i = 0; i < raw.size(); ++i) {
            out.emplace_back(BigInt(keel::move(raw[i].prime)), keel::as<keel::i32>(raw[i].exponent));
        }
        return out;
    }

    bool sqrtExact(BigInt &out) const { return v_.sqrt_exact(out.v_); }
    keel::u64 hashBits() const noexcept { return v_.hash_bits(); }

private:
    keel::bignum::BigInt v_;
};

} // namespace numkit::cas
