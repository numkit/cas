// poly/modcpoly.hpp — polynomials over the quotient field Q[t]/(c).
#pragma once

#include <numkit/cas/poly/upoly.hpp>

#include <cstddef>
#include <vector>

namespace numkit::cas {

// ============================================================
// ModCRing — the quotient ring Q[t]/(c(t)) as a coefficient FIELD.
//
// Contract: c is irreducible over Q (verifying needs factorization,
// which does not exist yet); with c irreducible every nonzero element
// is invertible. A linear c degenerates to plain Q. Elements are
// Q[t]-polynomials canonically reduced modulo the monic associate of
// c; irreducibility of c also makes the representation unique.
// ============================================================
class ModCRing
{
public:
    explicit ModCRing(UPoly c);

    const UPoly &modulus() const { return c_; }
    std::size_t dim() const { return static_cast<std::size_t>(c_.deg()); }

    UPoly reduce(const UPoly &a) const { return a % c_; }
    UPoly add(const UPoly &a, const UPoly &b) const;
    UPoly sub(const UPoly &a, const UPoly &b) const;
    UPoly neg(const UPoly &a) const;
    UPoly mul(const UPoly &a, const UPoly &b) const;
    UPoly div(const UPoly &a, const UPoly &b) const;
    UPoly inv(const UPoly &a) const; // asserts gcd(a, c) == 1

    bool isOne(const UPoly &a) const;

    const UPoly &zero() const { return zero_; }
    const UPoly &one() const { return one_; }

private:
    UPoly c_;
    UPoly zero_;
    UPoly one_;
};

// ============================================================
// ModCPoly — dense univariate polynomial (variable x) with
// coefficients in a ModCRing. Ascending, trimmed; zero has no ring
// attached (a null value, comparable for zero-ness only). All binary
// operations assert a common ring in debug builds.
// ============================================================
class ModCPoly
{
public:
    ModCPoly() = default;
    ModCPoly(const ModCRing &ring, std::vector<UPoly> coeffs);

    static ModCPoly constant(const ModCRing &ring, UPoly c0);
    static ModCPoly monomial(const ModCRing &ring, UPoly c0, std::size_t exp);

    bool hasRing() const { return ring_ != nullptr; }
    const ModCRing &ring() const;
    int deg() const { return static_cast<int>(c_.size()) - 1; }
    bool isZero() const { return c_.empty(); }
    UPoly coeff(std::size_t i) const
    {
        return i < c_.size() ? c_[i] : (ring_ != nullptr ? ring_->zero() : UPoly());
    }
    const UPoly &lc() const;

    friend ModCPoly operator+(const ModCPoly &a, const ModCPoly &b);
    friend ModCPoly operator-(const ModCPoly &a, const ModCPoly &b);
    friend ModCPoly operator*(const ModCPoly &a, const ModCPoly &b);
    ModCPoly operator-() const;

    // Field division: a = q*b + r, deg(r) < deg(b); b != 0.
    static void divMod(const ModCPoly &a, const ModCPoly &b,
                       ModCPoly &q, ModCPoly &r);

    // Monic greatest common divisor (Euclid over the coefficient field).
    static ModCPoly gcd(const ModCPoly &a, const ModCPoly &b);

    friend bool operator==(const ModCPoly &a, const ModCPoly &b);
    friend bool operator!=(const ModCPoly &a, const ModCPoly &b);

    // "p0|p1|..." with each coefficient an ascending rational csv —
    // used by tests and debugging.
    std::string toString() const;

private:
    friend struct ModCPolyOps;
    // Ring compatibility check; a default-constructed (ringless) zero is
    // the zero of any ring.
    static void checkSameRing(const ModCPoly &a, const ModCPoly &b);
    void trim();
    void makeMonic();

    const ModCRing *ring_ = nullptr;
    std::vector<UPoly> c_;
};

} // namespace numkit::cas
