// poly/upoly.hpp — dense univariate polynomial over Q (exact arithmetic).
#pragma once

#include <numkit/cas/num/rational.hpp>

#include <cstdint>
#include <string>
#include <vector>

namespace numkit::cas {

// ============================================================
// UPoly — dense univariate polynomial over the rationals.
//
// Representation: ascending coefficient vector c_[i] * x^i, trimmed
// (no trailing zeros); the zero polynomial is the empty vector.
// deg() of zero is -1.
//
// All arithmetic is exact. gcd is monic (gcd of anything with zero is
// the monic associate of the other operand). Resultant follows the
// standard conventions: res(a, b) = 1 for nonzero constants a, b;
// res with a zero operand is 0.
// ============================================================
class UPoly
{
public:
    UPoly() = default;
    explicit UPoly(Rational c);
    explicit UPoly(std::vector<Rational> coeffs);
    static UPoly monomial(Rational c, std::uint64_t exp); // c * x^exp

    int deg() const { return static_cast<int>(c_.size()) - 1; }
    bool isZero() const { return c_.empty(); }
    bool isConst() const { return c_.size() <= 1; }
    Rational coeff(std::size_t i) const
    {
        return i < c_.size() ? c_[i] : Rational(std::int64_t{0});
    }
    const Rational &lc() const; // asserts !isZero
    const std::vector<Rational> &coeffs() const { return c_; }

    Rational eval(const Rational &x) const;

    friend UPoly operator+(const UPoly &a, const UPoly &b);
    friend UPoly operator-(const UPoly &a, const UPoly &b);
    friend UPoly operator*(const UPoly &a, const UPoly &b);
    friend UPoly operator*(const UPoly &a, const Rational &k);
    friend UPoly operator*(const Rational &k, const UPoly &a);
    UPoly operator-() const;

    // Exact field division: a = q*b + r with deg(r) < deg(b); b != 0.
    static void divMod(const UPoly &a, const UPoly &b, UPoly &q, UPoly &r);

    UPoly derivative() const;
    UPoly powUInt(std::uint64_t n) const;

    // Monic greatest common divisor (Euclid over Q).
    static UPoly gcd(const UPoly &a, const UPoly &b);

    // A / gcd(A, A'), up to a rational scalar.
    UPoly squarefreePart() const;

    // Yun's squarefree decomposition (char 0). Returns the vector
    // (F_1, F_2, ..., F_k) so that A == lc(A) * F_1^1 * ... * F_k^k,
    // each F_i monic and squarefree; an entry equal to 1 means there is
    // no factor of that multiplicity.
    std::vector<UPoly> squarefreeDecomposition() const;

    // Resultant res_x(a, b) via the exact Euclidean recursion.
    static Rational resultant(const UPoly &a, const UPoly &b);

    friend bool operator==(const UPoly &a, const UPoly &b);
    friend bool operator!=(const UPoly &a, const UPoly &b);

    // Human-readable descending form, e.g. "x^3 - 3/2*x + 4".
    std::string toString(const char *var = "x") const;

private:
    void trim();
    void makeMonic();

    std::vector<Rational> c_;
};

} // namespace numkit::cas
