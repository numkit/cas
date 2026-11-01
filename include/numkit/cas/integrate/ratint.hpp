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

struct DefiniteBound
{
    Expr var;
    Expr a;
    Expr b;
};

// Iterated indefinite integration int ... int f(vars) d(vars[0]) ... d(vars[k-1]),
// certified by verifying the mixed partial derivative
// d^k F / (d(vars[k-1]) ... d(vars[0])) == f.
RationalIntegral integrateMulti(Ctx &c, Expr f, const std::vector<Expr> &vars,
                                Budget *budget = nullptr);

// Iterated definite integration from innermost bound `bounds[0]` to
// outermost bound `bounds.back()`:
//   int_{a_{k-1}}^{b_{k-1}} ... int_{a_0}^{b_0} f d(var_0) ... d(var_{k-1})
// where inner limits `a_i, b_i` may depend on outer integration variables
// `var_{i+1}, ..., var_{k-1}` (triangles, disks, tetrahedra, spheres, etc.).
DefiniteIntegral definiteIntegrateMulti(
    Ctx &c, Expr f, const std::vector<DefiniteBound> &bounds,
    Budget *budget = nullptr);

// Line integral of the 1st kind (with respect to arc length ds):
//   int_C f(vars) ds = int_a^b f(r(t)) * ||r'(t)|| dt
DefiniteIntegral lineIntegralScalar(Ctx &c, Expr f,
                                    const std::vector<Expr> &vars,
                                    const std::vector<Expr> &curve, Expr t,
                                    Expr a, Expr b, Budget *budget = nullptr);

// Line integral of the 2nd kind (work/circulation of vector field F along C):
//   int_C F(r) . dr = int_a^b sum_{i=0}^{n-1} F_i(r(t)) * r_i'(t) dt
DefiniteIntegral lineIntegralVector(Ctx &c, const std::vector<Expr> &field,
                                    const std::vector<Expr> &vars,
                                    const std::vector<Expr> &curve, Expr t,
                                    Expr a, Expr b, Budget *budget = nullptr);

inline DefiniteIntegral lineIntegral(Ctx &c, Expr f,
                                     const std::vector<Expr> &vars,
                                     const std::vector<Expr> &curve, Expr t,
                                     Expr a, Expr b, Budget *budget = nullptr)
{
    return lineIntegralScalar(c, f, vars, curve, t, a, b, budget);
}

inline DefiniteIntegral lineIntegral(Ctx &c, const std::vector<Expr> &field,
                                     const std::vector<Expr> &vars,
                                     const std::vector<Expr> &curve, Expr t,
                                     Expr a, Expr b, Budget *budget = nullptr)
{
    return lineIntegralVector(c, field, vars, curve, t, a, b, budget);
}

// Surface integral of the 1st kind (with respect to surface area element dS):
//   iint_S f(vars) dS = int_{vBound.a}^{vBound.b} int_{uBound.a}^{uBound.b}
//                         f(r(u, v)) * ||dr/du x dr/dv|| du dv
// where `vars` = {x, y, z}, `surface` = {r_x(u, v), r_y(u, v), r_z(u, v)},
// `uBound` is the inner parameter bound (whose limits may depend on `vBound.var`),
// and `vBound` is the outer parameter bound.
DefiniteIntegral surfaceIntegralScalar(Ctx &c, Expr f,
                                       const std::vector<Expr> &vars,
                                       const std::vector<Expr> &surface,
                                       const DefiniteBound &uBound,
                                       const DefiniteBound &vBound,
                                       Budget *budget = nullptr);

// Surface integral of the 2nd kind (flux of vector field F across S oriented
// by N = dr/du x dr/dv):
//   iint_S F(r) . dS = int_{vBound.a}^{vBound.b} int_{uBound.a}^{uBound.b}
//                        F(r(u, v)) . (dr/du x dr/dv) du dv
DefiniteIntegral surfaceIntegralVector(Ctx &c, const std::vector<Expr> &field,
                                       const std::vector<Expr> &vars,
                                       const std::vector<Expr> &surface,
                                       const DefiniteBound &uBound,
                                       const DefiniteBound &vBound,
                                       Budget *budget = nullptr);

inline DefiniteIntegral surfaceIntegral(Ctx &c, Expr f,
                                        const std::vector<Expr> &vars,
                                        const std::vector<Expr> &surface,
                                        const DefiniteBound &uBound,
                                        const DefiniteBound &vBound,
                                        Budget *budget = nullptr)
{
    return surfaceIntegralScalar(c, f, vars, surface, uBound, vBound, budget);
}

inline DefiniteIntegral surfaceIntegral(Ctx &c, const std::vector<Expr> &field,
                                        const std::vector<Expr> &vars,
                                        const std::vector<Expr> &surface,
                                        const DefiniteBound &uBound,
                                        const DefiniteBound &vBound,
                                        Budget *budget = nullptr)
{
    return surfaceIntegralVector(c, field, vars, surface, uBound, vBound,
                                 budget);
}

struct ParametricCurveSegment
{
    std::vector<Expr> curve;
    Expr t;
    Expr a;
    Expr b;
};

struct ParametricSurfacePatch
{
    std::vector<Expr> surface;
    DefiniteBound uBound;
    DefiniteBound vBound;
};

struct IntegralTheoremResult
{
    bool proved = false;
    Expr lhs; // boundary integral (circulation or flux)
    Expr rhs; // interior integral (curl or divergence integral)
    std::string reason;
};

// Symbolic verification of Green's theorem in the plane:
//   oint_{dD} (P dx + Q dy) == iint_D (dQ/dx - dP/dy) dA
IntegralTheoremResult verifyGreenTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<ParametricCurveSegment> &boundaryCurves,
    const std::vector<DefiniteBound> &domainBounds, Budget *budget = nullptr);

inline IntegralTheoremResult verifyGreenTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<Expr> &boundaryCurve, Expr t, Expr a, Expr b,
    const std::vector<DefiniteBound> &domainBounds, Budget *budget = nullptr)
{
    return verifyGreenTheorem(
        c, field, vars, {ParametricCurveSegment{boundaryCurve, t, a, b}},
        domainBounds, budget);
}

// Symbolic verification of Kelvin-Stokes' theorem in R^3:
//   oint_{dS} F . dr == iint_S (curl F) . dS
IntegralTheoremResult verifyStokesTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<ParametricCurveSegment> &boundaryCurves,
    const std::vector<Expr> &surface, const DefiniteBound &uBound,
    const DefiniteBound &vBound, Budget *budget = nullptr);

inline IntegralTheoremResult verifyStokesTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<Expr> &boundaryCurve, Expr t, Expr a, Expr b,
    const std::vector<Expr> &surface, const DefiniteBound &uBound,
    const DefiniteBound &vBound, Budget *budget = nullptr)
{
    return verifyStokesTheorem(
        c, field, vars, {ParametricCurveSegment{boundaryCurve, t, a, b}},
        surface, uBound, vBound, budget);
}

// Symbolic verification of the Gauss-Ostrogradsky divergence theorem in R^3:
//   oiint_{dV} F . dS == iiint_V (div F) dV
IntegralTheoremResult verifyGaussDivergenceTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<ParametricSurfacePatch> &boundaryPatches,
    const std::vector<DefiniteBound> &volumeBounds, Budget *budget = nullptr);

// Overload with a curvilinear volume coordinate transformation `volumeMap`
// (e.g. spherical or cylindrical coordinates) whose Jacobian determinant
// |det(d(vars)/d(paramVars))| is computed symbolically.
IntegralTheoremResult verifyGaussDivergenceTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<ParametricSurfacePatch> &boundaryPatches,
    const std::vector<Expr> &volumeMap,
    const std::vector<DefiniteBound> &volumeBounds, Budget *budget = nullptr);

inline IntegralTheoremResult verifyGaussDivergenceTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<Expr> &closedSurface, const DefiniteBound &uBound,
    const DefiniteBound &vBound,
    const std::vector<DefiniteBound> &volumeBounds, Budget *budget = nullptr)
{
    return verifyGaussDivergenceTheorem(
        c, field, vars, {ParametricSurfacePatch{closedSurface, uBound, vBound}},
        volumeBounds, budget);
}

inline IntegralTheoremResult verifyGaussDivergenceTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<Expr> &closedSurface, const DefiniteBound &uBound,
    const DefiniteBound &vBound, const std::vector<Expr> &volumeMap,
    const std::vector<DefiniteBound> &volumeBounds, Budget *budget = nullptr)
{
    return verifyGaussDivergenceTheorem(
        c, field, vars, {ParametricSurfacePatch{closedSurface, uBound, vBound}},
        volumeMap, volumeBounds, budget);
}

// Factor the rational function e(var) over Q: returns the factored
// canonical product (content coefficients in front, irreducible
// factors with multiplicities as integer powers). Returns false when
// e is not a rational function of var (nothing factored, `out`
// untouched).
bool factorExpr(Ctx &c, Expr e, Expr var, Expr &out);

} // namespace numkit::cas
