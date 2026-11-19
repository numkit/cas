// poly/fppoly.hpp — dense univariate polynomials over F_p.
#pragma once

#include <keel/array.h>
#include <keel/core.h>
#include <numkit/cas/num/bigint.hpp>

#include <cstddef>
#include <cstdint>

namespace numkit::cas {

// ============================================================
// FpPoly — dense ascending polynomial over the prime field F_p.
//
// Contract: p is an odd prime below 2^31 (coefficients and their
// products fit uint64). Every polynomial carries its modulus; binary
// operations assert a common p in debug builds. The zero polynomial
// is the empty coefficient vector.
// ============================================================
class FpPoly
{
public:
    FpPoly() noexcept = default;
    FpPoly(const FpPoly &o) : p_(o.p_), c_(o.c_.clone()) {}
    FpPoly &operator=(const FpPoly &o)
    {
        if (this != &o) {
            p_ = o.p_;
            c_ = o.c_.clone();
        }
        return *this;
    }
    FpPoly(FpPoly &&) noexcept = default;
    FpPoly &operator=(FpPoly &&) noexcept = default;

    FpPoly(keel::u64 p, keel::Array<keel::u64> coeffs);

    static FpPoly constant(keel::u64 p, keel::u64 c);
    static FpPoly monomial(keel::u64 p, keel::u64 c, keel::usize exp);
    static FpPoly x(keel::u64 p);

    keel::u64 p() const { return p_; }
    bool hasP() const { return p_ != 0; }
    int deg() const { return static_cast<int>(c_.size()) - 1; }
    bool isZero() const { return c_.empty(); }
    bool isOne() const { return c_.size() == 1 && c_[0] == 1; }
    keel::u64 coeff(keel::usize i) const { return i < c_.size() ? c_[i] : 0; }
    keel::u64 lc() const; // asserts !isZero

    friend FpPoly operator+(const FpPoly &a, const FpPoly &b);
    friend FpPoly operator-(const FpPoly &a, const FpPoly &b);
    friend FpPoly operator*(const FpPoly &a, const FpPoly &b);
    FpPoly operator-() const;
    FpPoly operator*(keel::u64 k) const; // scalar

    // a = q*b + r, deg r < deg b; b != 0.
    static void divMod(const FpPoly &a, const FpPoly &b, FpPoly &q, FpPoly &r);
    friend FpPoly operator%(const FpPoly &a, const FpPoly &b);

    static FpPoly gcd(const FpPoly &a, const FpPoly &b); // monic gcd

    // Extended gcd: s*a + t*b == gcd(a, b) (monic gcd), for coprime
    // inputs the Bezout pair of the lifted Hensel step.
    static void extGcd(const FpPoly &a, const FpPoly &b, FpPoly &s, FpPoly &t);

    // this^e mod m (m nonzero), square-and-multiply over the BigInt
    // exponent so p^d-scale exponents work.
    FpPoly powMod(const BigInt &e, const FpPoly &m) const;

    keel::u64 eval(keel::u64 x0) const;
    FpPoly derivative() const;

    friend bool operator==(const FpPoly &a, const FpPoly &b);
    friend bool operator!=(const FpPoly &a, const FpPoly &b);

    // ── factorization over F_p ─────────────────────────────────
    // Complete factorization into monic irreducibles. Multiplicities
    // are dropped (the squarefree part of the input is factored).
    // Deterministic: the EDF randomizer is a fixed-seed PRNG.
    static keel::Array<FpPoly> factor(const FpPoly &f);

    // Irreducibility criterion for a monic squarefree g of degree d:
    // x^(p^d) = x (mod g) and gcd(x^(p^(d/q)) - x, g) = 1 for every
    // prime q dividing d. Usable as an independent checker of factor().
    bool isIrreducible() const;

    keel::usize size() const { return c_.size(); }
    const keel::Array<keel::u64> &coeffsAll() const { return c_; }

private:
    static void checkSameField(const FpPoly &a, const FpPoly &b);
    void trim();
    static keel::u64 invModP(keel::u64 a, keel::u64 p);
    // visible for the anonymous-namespace factoring helpers

    keel::u64 p_ = 0;
    keel::Array<keel::u64> c_;
};

} // namespace numkit::cas
