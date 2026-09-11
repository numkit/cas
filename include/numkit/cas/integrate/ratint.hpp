// integrate/ratint.hpp — rational function integration with certificate.
#pragma once

#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/poly/upoly.hpp>

#include <string>

namespace numkit::cas {

// ============================================================
// M0 vertical slice: integrate a rational function of one variable
// exactly, with the PROVED_SYMBOLIC certificate verified inside Q(x):
// every constructed piece (polynomial, rational, c*log(v), a*atan(u)
// with rational u) has an exact rational derivative, and their sum is
// checked against the integrand by cross-multiplication.
//
// Limitations of the M0 log part (honest Unevaluated otherwise):
//   - denominator factors must split over Q into linear factors
//     (rational roots found by a bounded rational-root search) and
//     irreducible quadratics whose 4c - b^2 is a positive rational
//     square (rational-coefficient arctangent form);
//   - anything else returns Unevaluated with a reason. The general
//     Rothstein-Trager/RootOf form with algebraic residues is C1.
// ============================================================
struct RationalIntegral
{
    enum class Status
    {
        Unevaluated,
        ProvedSymbolic,
    };

    Status status = Status::Unevaluated;
    Expr F;           // antiderivative; null unless ProvedSymbolic
    std::string reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Extract the rational function e(x) as an exact fraction num/den.
// Returns false when e is not rational in var (transcendental parts,
// other symbols, non-integer powers, zero to a negative power).
bool toRational(Ctx &c, Expr e, Expr var, UPoly &num, UPoly &den);

// Render a polynomial back into the expression DAG.
Expr toExpr(Ctx &c, const UPoly &p, Expr var);

// Hermite reduction: given N/D (any denominator, D != 0), split
//   N/D = d(Rn/Rd)/dx + g/S
// with S squarefree, deg g < deg S. Always succeeds.
struct HermiteResult
{
    UPoly rn, rd; // rational part antiderivative
    UPoly gn, S;  // residual with squarefree denominator
};
HermiteResult hermiteReduce(const UPoly &N, const UPoly &D);

// res_x(P - t*Q, M) as an exact polynomial in t (degree <= deg M),
// computed by evaluation-interpolation: specialization commutes with
// the resultant, so deg M + 1 rational evaluations of the ordinary
// Q[x] resultant plus Lagrange interpolation suffice.
UPoly resultantT(const UPoly &P, const UPoly &Q, const UPoly &M);

RationalIntegral integrateRational(Ctx &c, Expr f, Expr var);

// Factor the rational function e(var) over Q: returns the factored
// canonical product (content coefficients in front, irreducible
// factors with multiplicities as integer powers). Returns false when
// e is not a rational function of var (nothing factored, `out`
// untouched).
bool factorExpr(Ctx &c, Expr e, Expr var, Expr &out);

} // namespace numkit::cas
