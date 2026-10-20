// transform/laplace.hpp — symbolic unilateral Laplace and inverse Laplace transforms.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <string>

namespace numkit::cas {

struct LaplaceResult
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    Expr F;             // transformed expression in `s` (laplace) or `t` (ilaplace)
    std::string reason; // populated on Unevaluated

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Forward unilateral Laplace transform:
//   L{f(t)}(s) = int_0^inf f(t) * exp(-s * t) dt.
// Supports linearity, polynomial/half-integer powers of t, frequency-domain
// differentiation t^n * g(t) -> (-1)^n d^n/ds^n L{g}(s), first shifting
// theorem exp(a*t) * g(t) -> G(s - a), elementary and phase-shifted
// trigonometric and hyperbolic functions (including products and integer
// powers via product-to-sum reduction), and symbolic parameters.
LaplaceResult laplace(Ctx &c, Expr f, Expr t, Expr s,
                      Budget *budget = nullptr);

// Inverse Laplace transform L^{-1}{F(s)}(t), using exact partial fraction
// decomposition over Q[s] (via factorOverQ + extended Euclidean reduction +
// P-adic expansion for arbitrary-multiplicity linear poles and simple/double
// quadratic poles) as well as parametric symbolic pole/quadratic forms,
// certified by round-trip verification L{f(t)}(s) == F(s).
LaplaceResult ilaplace(Ctx &c, Expr F, Expr s, Expr t,
                       Budget *budget = nullptr);

} // namespace numkit::cas
