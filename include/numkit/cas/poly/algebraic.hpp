// poly/algebraic.hpp — real algebraic numbers (exact).
#pragma once

#include <numkit/cas/poly/sturm.hpp>

#include <vector>

namespace numkit::cas {

// ============================================================
// Algebraic — a real algebraic number: the unique root of a squarefree
// polynomial inside an isolating interval. Rational numbers are the
// canonical degenerate case: the linear polynomial x - r with the
// exact interval (r, r) — any linear polynomial or exact root found
// during isolation is normalized to this form.
//
// Comparison is exact: intervals are refined until they separate, with
// equality detection driven by the gcd of the defining polynomials
// (numbers defined by different polynomials may still be equal).
// ============================================================
class Algebraic
{
public:
    Algebraic();                    // exact zero
    explicit Algebraic(Rational r); // exact rational

    // p must be squarefree and non-constant; iv must isolate exactly one
    // root of p (strictly inside, or the exact rational root itself).
    Algebraic(UPoly p, RootInterval iv);

    static std::vector<Algebraic> realRoots(const UPoly &p);

    bool isRational() const { return poly_.deg() <= 1; }
    Rational rationalValue() const; // asserts isRational
    const UPoly &poly() const { return poly_; }
    const RootInterval &interval() const { return iv_; }

    int sign() const;
    bool isZero() const { return sign() == 0; }

    // Total order on real algebraic numbers.
    static int compare(const Algebraic &a, const Algebraic &b);

    void refineTo(const Rational &width);

    // Approximation for diagnostics/tests only.
    double approx() const;

private:
    static bool containsRoot(const UPoly &g, const std::vector<UPoly> &sturmG,
                             const Algebraic &a);
    int positionCompare(const Algebraic &other) const;
    void refineStep();

    UPoly poly_;      // squarefree, monic, degree >= 1
    RootInterval iv_; // isolating; exact (lo == hi) iff rational
};

} // namespace numkit::cas
