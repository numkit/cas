// num/bigint.hpp — arbitrary-precision integer, exact arithmetic layer.
#pragma once

#include <keel/array.h>
#include <keel/core.h>
#include <keel/string.h>
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <utility>

namespace numkit::cas {

// ============================================================
// BigInt — signed arbitrary-precision integer.
//
// Representation: signed magnitude, little-endian base-2^64 limbs
// with 2-limb (128-bit) Small Buffer Optimization (SBO) inline on the
// stack. Invariants: no trailing zero limbs; zero is the empty limb
// buffer with negative_ == false (no negative zero).
//
// Division/modulo follow C truncated semantics:
//   a == (a/b)*b + (a%b), |a%b| < |b|, sign(a%b) == sign(a) or zero.
// Division by zero is a caller contract violation (assert in debug).
// ============================================================
class BigInt
{
public:
    BigInt() noexcept = default;
    BigInt(keel::i64 v) noexcept;
    BigInt(keel::u64 v) noexcept; // non-negative

    template <typename T>
        requires(std::is_integral_v<T> && !std::is_same_v<T, bool> &&
                 std::is_signed_v<T> && !std::is_same_v<T, keel::i64>)
    BigInt(T v) noexcept : BigInt(static_cast<keel::i64>(v)) {}

    template <typename T>
        requires(std::is_integral_v<T> && !std::is_same_v<T, bool> &&
                 std::is_unsigned_v<T> && !std::is_same_v<T, keel::u64>)
    BigInt(T v) noexcept : BigInt(static_cast<keel::u64>(v)) {}

    // Strict decimal parse: optional sign, one or more digits, no whitespace.
    static bool tryParse(BigInt &out, keel::StringRef s);

    bool isZero() const noexcept { return limbs_.empty(); }
    bool isInline() const noexcept { return limbs_.isInline(); }
    int signum() const noexcept;
    bool isNegative() const noexcept { return negative_; }
    keel::usize bitLength() const noexcept;

    // Undefined on zero magnitude access to the low limb.
    keel::u64 lowLimb() const noexcept
    {
        return limbs_.empty() ? 0 : limbs_[0];
    }

    bool fitsInt64(keel::i64 &out) const noexcept;
    bool fitsUint64(keel::u64 &out) const noexcept;

    // Nearest IEEE-754 double (+/-INFINITY on overflow past 2^1024).
    keel::f64 toDouble() const noexcept;

    keel::String toString() const;

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

    BigInt operator<<(keel::usize bits) const;
    BigInt operator>>(keel::usize bits) const; // floor semantics for negatives

    static void divMod(const BigInt &a, const BigInt &b, BigInt &q, BigInt &r);
    static BigInt gcd(const BigInt &a, const BigInt &b); // non-negative result
    static BigInt powUInt(const BigInt &base, keel::u64 exp); // 0^0 == 1
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
    static keel::Array<std::pair<BigInt, int>> factorize(const BigInt &n);

    // Exact integer square root (false for negatives and non-squares).
    bool sqrtExact(BigInt &out) const;

    // Order-insensitive content hash for hash-consing (collisions are fine).
    keel::u64 hashBits() const;

private:
    // 2-limb (128-bit) Small Buffer Optimization container for base-2^64 limbs.
    class LimbVec
    {
    public:
        static constexpr keel::usize kInlineCap = 2;

        LimbVec() noexcept = default;

        ~LimbVec() noexcept
        {
            if (!isInline())
                delete[] heap_;
        }

        LimbVec(const LimbVec &o) : size_(o.size_)
        {
            if (o.size_ <= kInlineCap) {
                cap_ = static_cast<keel::u32>(kInlineCap);
                for (keel::u32 i = 0; i < o.size_; ++i)
                    inline_[i] = o.data()[i];
            } else {
                cap_ = o.size_;
                heap_ = new keel::u64[cap_];
                for (keel::u32 i = 0; i < o.size_; ++i)
                    heap_[i] = o.heap_[i];
            }
        }

        LimbVec(LimbVec &&o) noexcept : size_(o.size_), cap_(o.cap_)
        {
            if (o.isInline()) {
                for (keel::u32 i = 0; i < o.size_; ++i)
                    inline_[i] = o.inline_[i];
            } else {
                heap_ = o.heap_;
                o.heap_ = nullptr;
                o.cap_ = static_cast<keel::u32>(kInlineCap);
            }
            o.size_ = 0;
        }

        LimbVec &operator=(const LimbVec &o)
        {
            if (this == &o)
                return *this;
            if (o.size_ <= cap_) {
                keel::u64 *dst = data();
                const keel::u64 *src = o.data();
                for (keel::u32 i = 0; i < o.size_; ++i)
                    dst[i] = src[i];
                size_ = o.size_;
                return *this;
            }
            keel::u64 *fresh = new keel::u64[o.size_];
            const keel::u64 *src = o.data();
            for (keel::u32 i = 0; i < o.size_; ++i)
                fresh[i] = src[i];
            if (!isInline())
                delete[] heap_;
            heap_ = fresh;
            size_ = o.size_;
            cap_ = o.size_;
            return *this;
        }

        LimbVec &operator=(LimbVec &&o) noexcept
        {
            if (this == &o)
                return *this;
            if (!isInline())
                delete[] heap_;
            size_ = o.size_;
            cap_ = o.cap_;
            heap_ = nullptr;
            if (o.isInline()) {
                for (keel::u32 i = 0; i < o.size_; ++i)
                    inline_[i] = o.inline_[i];
            } else {
                heap_ = o.heap_;
                o.heap_ = nullptr;
                o.cap_ = static_cast<keel::u32>(kInlineCap);
            }
            o.size_ = 0;
            return *this;
        }

        bool isInline() const noexcept { return cap_ <= kInlineCap; }
        bool empty() const noexcept { return size_ == 0; }
        keel::usize size() const noexcept { return size_; }

        keel::u64 *data() noexcept
        {
            return isInline() ? inline_ : heap_;
        }
        const keel::u64 *data() const noexcept
        {
            return isInline() ? inline_ : heap_;
        }

        keel::u64 &operator[](keel::usize i) noexcept
        {
            assert(i < size_);
            return data()[i];
        }
        const keel::u64 &operator[](keel::usize i) const noexcept
        {
            assert(i < size_);
            return data()[i];
        }

        keel::u64 &back() noexcept
        {
            assert(size_ > 0);
            return data()[size_ - 1];
        }
        const keel::u64 &back() const noexcept
        {
            assert(size_ > 0);
            return data()[size_ - 1];
        }

        const keel::u64 *begin() const noexcept { return data(); }
        const keel::u64 *end() const noexcept { return data() + size_; }

        void clear() noexcept { size_ = 0; }

        void pop_back() noexcept
        {
            assert(size_ > 0);
            --size_;
        }

        void reserve(keel::usize newCap)
        {
            if (newCap <= cap_)
                return;
            const keel::u32 target = static_cast<keel::u32>(
                std::max<keel::usize>(newCap, static_cast<keel::usize>(cap_) * 2));
            keel::u64 *fresh = new keel::u64[target];
            const keel::u64 *src = data();
            for (keel::u32 i = 0; i < size_; ++i)
                fresh[i] = src[i];
            if (!isInline())
                delete[] heap_;
            heap_ = fresh;
            cap_ = target;
        }

        void push_back(keel::u64 v)
        {
            if (size_ == cap_)
                reserve(static_cast<keel::usize>(cap_) * 2);
            data()[size_++] = v;
        }

        void assign(keel::usize count, keel::u64 v)
        {
            if (count > cap_)
                reserve(count);
            keel::u64 *dst = data();
            for (keel::usize i = 0; i < count; ++i)
                dst[i] = v;
            size_ = static_cast<keel::u32>(count);
        }

        bool operator==(const LimbVec &o) const noexcept
        {
            if (size_ != o.size_)
                return false;
            const keel::u64 *a = data();
            const keel::u64 *b = o.data();
            for (keel::u32 i = 0; i < size_; ++i)
                if (a[i] != b[i])
                    return false;
            return true;
        }

    private:
        keel::u64 inline_[kInlineCap] = {0, 0};
        keel::u64 *heap_ = nullptr;
        keel::u32 size_ = 0;
        keel::u32 cap_ = static_cast<keel::u32>(kInlineCap);
    };

    void normalize() noexcept;
    int compareMagnitude(const BigInt &o) const noexcept;
    static BigInt addMagnitude(const BigInt &a, const BigInt &b);
    static BigInt subMagnitude(const BigInt &a, const BigInt &b); // |a| >= |b|

    LimbVec limbs_;
    bool negative_ = false;
};

} // namespace numkit::cas
