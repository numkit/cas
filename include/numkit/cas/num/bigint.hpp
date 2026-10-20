// num/bigint.hpp — arbitrary-precision integer, exact arithmetic layer.
#pragma once

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

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
    BigInt(std::int64_t v) noexcept;
    BigInt(std::uint64_t v) noexcept; // non-negative
    BigInt(int v) noexcept : BigInt(static_cast<std::int64_t>(v)) {}

    // Strict decimal parse: optional sign, one or more digits, no whitespace.
    static bool tryParse(BigInt &out, const std::string &s);

    bool isZero() const noexcept { return limbs_.empty(); }
    bool isInline() const noexcept { return limbs_.isInline(); }
    int signum() const noexcept;
    bool isNegative() const noexcept { return negative_; }
    std::size_t bitLength() const noexcept;

    // Undefined on zero magnitude access to the low limb.
    std::uint64_t lowLimb() const noexcept
    {
        return limbs_.empty() ? 0 : limbs_[0];
    }

    bool fitsInt64(std::int64_t &out) const noexcept;
    bool fitsUint64(std::uint64_t &out) const noexcept;

    // Nearest IEEE-754 double (+/-INFINITY on overflow past 2^1024).
    double toDouble() const noexcept;

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
    // 2-limb (128-bit) Small Buffer Optimization container for base-2^64 limbs.
    class LimbVec
    {
    public:
        static constexpr std::size_t kInlineCap = 2;

        LimbVec() noexcept = default;

        ~LimbVec() noexcept
        {
            if (!isInline())
                delete[] heap_;
        }

        LimbVec(const LimbVec &o) : size_(o.size_)
        {
            if (o.size_ <= kInlineCap) {
                cap_ = static_cast<std::uint32_t>(kInlineCap);
                for (std::uint32_t i = 0; i < o.size_; ++i)
                    inline_[i] = o.data()[i];
            } else {
                cap_ = o.size_;
                heap_ = new std::uint64_t[cap_];
                for (std::uint32_t i = 0; i < o.size_; ++i)
                    heap_[i] = o.heap_[i];
            }
        }

        LimbVec(LimbVec &&o) noexcept : size_(o.size_), cap_(o.cap_)
        {
            if (o.isInline()) {
                for (std::uint32_t i = 0; i < o.size_; ++i)
                    inline_[i] = o.inline_[i];
            } else {
                heap_ = o.heap_;
                o.heap_ = nullptr;
                o.cap_ = static_cast<std::uint32_t>(kInlineCap);
            }
            o.size_ = 0;
        }

        LimbVec &operator=(const LimbVec &o)
        {
            if (this == &o)
                return *this;
            if (o.size_ <= cap_) {
                std::uint64_t *dst = data();
                const std::uint64_t *src = o.data();
                for (std::uint32_t i = 0; i < o.size_; ++i)
                    dst[i] = src[i];
                size_ = o.size_;
                return *this;
            }
            std::uint64_t *fresh = new std::uint64_t[o.size_];
            const std::uint64_t *src = o.data();
            for (std::uint32_t i = 0; i < o.size_; ++i)
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
                for (std::uint32_t i = 0; i < o.size_; ++i)
                    inline_[i] = o.inline_[i];
            } else {
                heap_ = o.heap_;
                o.heap_ = nullptr;
                o.cap_ = static_cast<std::uint32_t>(kInlineCap);
            }
            o.size_ = 0;
            return *this;
        }

        bool isInline() const noexcept { return cap_ <= kInlineCap; }
        bool empty() const noexcept { return size_ == 0; }
        std::size_t size() const noexcept { return size_; }

        std::uint64_t *data() noexcept
        {
            return isInline() ? inline_ : heap_;
        }
        const std::uint64_t *data() const noexcept
        {
            return isInline() ? inline_ : heap_;
        }

        std::uint64_t &operator[](std::size_t i) noexcept
        {
            assert(i < size_);
            return data()[i];
        }
        const std::uint64_t &operator[](std::size_t i) const noexcept
        {
            assert(i < size_);
            return data()[i];
        }

        std::uint64_t &back() noexcept
        {
            assert(size_ > 0);
            return data()[size_ - 1];
        }
        const std::uint64_t &back() const noexcept
        {
            assert(size_ > 0);
            return data()[size_ - 1];
        }

        const std::uint64_t *begin() const noexcept { return data(); }
        const std::uint64_t *end() const noexcept { return data() + size_; }

        void clear() noexcept { size_ = 0; }

        void pop_back() noexcept
        {
            assert(size_ > 0);
            --size_;
        }

        void reserve(std::size_t newCap)
        {
            if (newCap <= cap_)
                return;
            const std::uint32_t target = static_cast<std::uint32_t>(
                std::max<std::size_t>(newCap, static_cast<std::size_t>(cap_) * 2));
            std::uint64_t *fresh = new std::uint64_t[target];
            const std::uint64_t *src = data();
            for (std::uint32_t i = 0; i < size_; ++i)
                fresh[i] = src[i];
            if (!isInline())
                delete[] heap_;
            heap_ = fresh;
            cap_ = target;
        }

        void push_back(std::uint64_t v)
        {
            if (size_ == cap_)
                reserve(static_cast<std::size_t>(cap_) * 2);
            data()[size_++] = v;
        }

        void assign(std::size_t count, std::uint64_t v)
        {
            if (count > cap_)
                reserve(count);
            std::uint64_t *dst = data();
            for (std::size_t i = 0; i < count; ++i)
                dst[i] = v;
            size_ = static_cast<std::uint32_t>(count);
        }

        bool operator==(const LimbVec &o) const noexcept
        {
            if (size_ != o.size_)
                return false;
            const std::uint64_t *a = data();
            const std::uint64_t *b = o.data();
            for (std::uint32_t i = 0; i < size_; ++i)
                if (a[i] != b[i])
                    return false;
            return true;
        }

    private:
        std::uint64_t inline_[kInlineCap] = {0, 0};
        std::uint64_t *heap_ = nullptr;
        std::uint32_t size_ = 0;
        std::uint32_t cap_ = static_cast<std::uint32_t>(kInlineCap);
    };

    void normalize() noexcept;
    int compareMagnitude(const BigInt &o) const noexcept;
    static BigInt addMagnitude(const BigInt &a, const BigInt &b);
    static BigInt subMagnitude(const BigInt &a, const BigInt &b); // |a| >= |b|

    LimbVec limbs_;
    bool negative_ = false;
};

} // namespace numkit::cas
