// integrate/ratint.hpp — rational function integration with certificate.
#pragma once

#include <numkit/cas/core/budget.hpp>
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

RationalIntegral integrateRational(Ctx &c, Expr f, Expr var,
                                   Budget *budget = nullptr);

// Unified symbolic integration cascade (C1 item 34):
//   1. AOT Rubi rule engine fast-path (`rubiApply(sliceTables(), ...)`).
//   2. Algebraic & Liouvillian kernel (`integrateRational`: Hermite +
//      Rothstein-Trager + Rioboo + exp/log/tan/radical storeys).
//   3. Constant-factor pull-out (`var`-free factors) and additive
//      linearity over `Add`, allowing mixed sums where individual
//      summands are handled by either Rubi or the algebraic/Liouvillian
//      kernel.
RationalIntegral integrate(Ctx &c, Expr f, Expr var,
                           Budget *budget = nullptr);

struct DefiniteIntegral
{
    enum class Status
    {
        Unevaluated,
        ProvedSymbolic,
        Divergent,
    };

    Status status = Status::Unevaluated;
    Expr value; // definite integral value when ProvedSymbolic
    Expr F;     // certified indefinite antiderivative used
    std::string reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Certified definite and improper symbolic integration int_a^b f(var) d(var):
//   1. Interior pole detection on (a, b) via polynomial denominator root
//      isolation (`solveRealRoots`) + Laurent pole verification (`limit`).
//   2. Certified indefinite antiderivative F(var) via `integrate`.
//   3. Endpoint evaluation lim_{var -> b^-} F(var) - lim_{var -> a^+} F(var)
//      with real log|u| branch realization and symbolic infinity support
//      (`inf`/`oo`/`infinity` and `-inf`).
DefiniteIntegral definiteIntegrate(Ctx &c, Expr f, Expr var, Expr a, Expr b,
                                   Budget *budget = nullptr);

// Factor the rational function e(var) over Q: returns the factored
// canonical product (content coefficients in front, irreducible
// factors with multiplicities as integer powers). Returns false when
// e is not a rational function of var (nothing factored, `out`
// untouched).
bool factorExpr(Ctx &c, Expr e, Expr var, Expr &out);

} // namespace numkit::cas
