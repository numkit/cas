// poly/fppoly.hpp — dense univariate polynomials over F_p.
#pragma once

#include <numkit/cas/num/bigint.hpp>

#include <cstddef>
#include <cstdint>
#include <vector>

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
    FpPoly() = default;
    FpPoly(std::uint64_t p, std::vector<std::uint64_t> coeffs);

    static FpPoly constant(std::uint64_t p, std::uint64_t c);
    static FpPoly monomial(std::uint64_t p, std::uint64_t c, std::size_t exp);
    static FpPoly x(std::uint64_t p);

    std::uint64_t p() const { return p_; }
    bool hasP() const { return p_ != 0; }
    int deg() const { return static_cast<int>(c_.size()) - 1; }
    bool isZero() const { return c_.empty(); }
    bool isOne() const { return c_.size() == 1 && c_[0] == 1; }
    std::uint64_t coeff(std::size_t i) const { return i < c_.size() ? c_[i] : 0; }
    std::uint64_t lc() const; // asserts !isZero

    friend FpPoly operator+(const FpPoly &a, const FpPoly &b);
    friend FpPoly operator-(const FpPoly &a, const FpPoly &b);
    friend FpPoly operator*(const FpPoly &a, const FpPoly &b);
    FpPoly operator-() const;
    FpPoly operator*(std::uint64_t k) const; // scalar

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

    std::uint64_t eval(std::uint64_t x0) const;
    FpPoly derivative() const;

    friend bool operator==(const FpPoly &a, const FpPoly &b);
    friend bool operator!=(const FpPoly &a, const FpPoly &b);

    // ── factorization over F_p ─────────────────────────────────
    // Complete factorization into monic irreducibles. Multiplicities
    // are dropped (the squarefree part of the input is factored).
    // Deterministic: the EDF randomizer is a fixed-seed PRNG.
    static std::vector<FpPoly> factor(const FpPoly &f);

    // Irreducibility criterion for a monic squarefree g of degree d:
    // x^(p^d) = x (mod g) and gcd(x^(p^(d/q)) - x, g) = 1 for every
    // prime q dividing d. Usable as an independent checker of factor().
    bool isIrreducible() const;

    std::size_t size() const { return c_.size(); }
    const std::vector<std::uint64_t> &coeffsAll() const { return c_; }

private:
    static void checkSameField(const FpPoly &a, const FpPoly &b);
    void trim();
    static std::uint64_t invModP(std::uint64_t a, std::uint64_t p);
    // visible for the anonymous-namespace factoring helpers

    std::uint64_t p_ = 0;
    std::vector<std::uint64_t> c_;
};

} // namespace numkit::cas
