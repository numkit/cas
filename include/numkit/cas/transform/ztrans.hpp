// transform/ztrans.hpp — symbolic unilateral Z-transform, inverse Z-transform,
// and certified linear recurrence equation solver (rsolve / rsolveIVP).
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <string>
#include <vector>

namespace numkit::cas {

struct ZTransResult
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    Expr F;             // transformed expression in `z` (ztrans) or `n` (iztrans)
    std::string reason; // populated on Unevaluated

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Forward unilateral Z-transform:
//   Z{f(n)}(z) = sum_{n=0}^inf f(n) * z^(-n).
// Supports linearity, geometric/exponential sequences a^n and exp(b*n),
// polynomial multiplication n^k * g(n) -> (-z * d/dz)^k Z{g}(z), discrete
// impulse kroneckerDelta(n - k) -> z^(-k), damped trigonometric and
// hyperbolic sequences r^n * sin/cos(w*n + phi), r^n * sinh/cosh(a*n + phi),
// and symbolic parameters.
ZTransResult ztrans(Ctx &c, Expr f, Expr n, Expr z, Budget *budget = nullptr);

// Inverse unilateral Z-transform Z^{-1}{F(z)}(n), using partial fraction
// decomposition of F(z)/z over Q[z] (arbitrary-multiplicity rational poles,
// quadratic radical poles such as Fibonacci z/(z^2 - z - 1), and complex-
// conjugate oscillatory poles), as well as parametric forms, certified by
// round-trip verification Z{f(n)}(z) == F(z).
ZTransResult iztrans(Ctx &c, Expr F, Expr z, Expr n, Budget *budget = nullptr);

struct RsolveResult
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    Expr y;             // closed-form sequence y(n)
    std::string reason; // populated on Unevaluated

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Solve a K-th order linear constant-coefficient recurrence equation:
//   coeffs[0]*y(n) + coeffs[1]*y(n+1) + ... + coeffs[K]*y(n+K) = rhs(n)
// with integration constants C1, ..., CK, certified by substituting y(n+k)
// back into the recurrence.
RsolveResult rsolve(Ctx &c, const std::vector<Expr> &coeffs, Expr rhs, Expr n,
                    Budget *budget = nullptr);

// Solve the initial-value problem for a K-th order linear recurrence:
//   coeffs[0]*y(n) + ... + coeffs[K]*y(n+K) = rhs(n),
//   y(0) = initVals[0], ..., y(K-1) = initVals[K-1],
// certified by verifying both the recurrence and all K initial values.
RsolveResult rsolveIVP(Ctx &c, const std::vector<Expr> &coeffs, Expr rhs,
                       Expr n, const std::vector<Expr> &initVals,
                       Budget *budget = nullptr);

} // namespace numkit::cas
