// poly/modcpoly.hpp — polynomials over the quotient field Q[t]/(c).
#pragma once

#include <keel/array.h>
#include <keel/core.h>
#include <keel/string.h>
#include <numkit/cas/poly/upoly.hpp>


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
    keel::usize dim() const { return keel::as<keel::usize>(c_.deg()); }

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
    ModCPoly() noexcept = default;
    ModCPoly(const ModCPoly &o) : ring_(o.ring_), c_(o.c_.clone()) {}
    ModCPoly &operator=(const ModCPoly &o)
    {
        if (this != &o) {
            ring_ = o.ring_;
            c_ = o.c_.clone();
        }
        return *this;
    }
    ModCPoly(ModCPoly &&) noexcept = default;
    ModCPoly &operator=(ModCPoly &&) noexcept = default;

    ModCPoly(const ModCRing &ring, keel::Array<UPoly> coeffs);

    static ModCPoly constant(const ModCRing &ring, UPoly c0);
    static ModCPoly monomial(const ModCRing &ring, UPoly c0, keel::usize exp);

    bool hasRing() const { return ring_ != nullptr; }
    const ModCRing &ring() const;
    keel::i32 deg() const { return keel::as<keel::i32>(c_.size()) - 1; }
    bool isZero() const { return c_.empty(); }
    UPoly coeff(keel::usize i) const
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
    keel::String toString() const;

private:
    friend struct ModCPolyOps;
    // Ring compatibility check; a default-constructed (ringless) zero is
    // the zero of any ring.
    static void checkSameRing(const ModCPoly &a, const ModCPoly &b);
    void trim();
    void makeMonic();

    const ModCRing *ring_ = nullptr;
    keel::Array<UPoly> c_;
};

} // namespace numkit::cas
