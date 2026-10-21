// core/series.hpp — truncated Taylor/Laurent power series and symbolic limits.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <string>

namespace numkit::cas {

// Truncated Taylor polynomial of `f` in `var` around `x0` up to degree
// `order` (inclusive, i.e. sum_{k=0}^{order} c_k * (var - x0)^k).
// Uses truncated Laurent series algebra in t = var - x0 to cancel
// removable singularities (e.g. (sin(x) - x)/x^3 at x0 = 0), falling
// back to exact iterated differentiation f^(k)(x0)/k! when needed.
// Returns a null Expr if `order < 0`, if `f` has a pole at `x0`, or if
// a non-analytic branch point or budget exhaustion is encountered.
Expr taylor(Ctx &c, Expr f, Expr var, Expr x0, int order,
            Budget *budget = nullptr);

// Truncated Laurent series of `f` in `var` around `x0` up to degree
// `order` (inclusive, including principal-part terms (var - x0)^k for
// k < 0 when `f` has a pole of finite order at `x0`).
Expr laurent(Ctx &c, Expr f, Expr var, Expr x0, int order,
             Budget *budget = nullptr);

// Symbolic residue Res(f, var = z0) = [(var - z0)^(-1)] f(var) at a
// finite point `z0` or at `inf`/`oo`/`infinity` (where Res_{z=inf} f(z) =
// -Res_{t=0} t^(-2) f(1/t)). Returns a null Expr if `f` has an essential
// singularity or branch point at `z0` or if the budget is exhausted.
Expr residue(Ctx &c, Expr f, Expr var, Expr z0, Budget *budget = nullptr);

struct LimitResult
{
    enum class Status
    {
        Unevaluated,
        Proved,
        Divergent, // pole of finite order at x0
    };

    Status status = Status::Unevaluated;
    Expr value; // limit value when status == Proved; null otherwise
    int poleOrder = 0; // positive pole order when status == Divergent
    std::string reason;

    bool proved() const { return status == Status::Proved; }
};

// Two-sided symbolic limit lim_{var -> x0} f(var):
//   1. Truncated Laurent series expansion around t = var - x0 (canceling
//      arbitrary-order zero/pole indeterminate forms 0/0, inf - inf, etc.).
//   2. Product-to-quotient rewrite for 0 * log(0) indeterminate forms and
//      bounded L'Hopital's rule on 0/0 or inf/inf quotient forms.
//   3. Recognizes symbolic infinity endpoints `inf`/`oo`/`infinity` and
//      `-inf`/`-oo`/`-infinity`, dispatching to `limitAtInfinity`.
LimitResult limit(Ctx &c, Expr f, Expr var, Expr x0,
                  Budget *budget = nullptr);

// One-sided symbolic limit lim_{var -> x0^+} f(var) (dir > 0) or
// lim_{var -> x0^-} f(var) (dir < 0), supporting square-root Puiseux
// branch points at x0 via t = sqrt(dir * (var - x0)).
LimitResult limitOneSided(Ctx &c, Expr f, Expr var, Expr x0, int dir,
                          Budget *budget = nullptr);

// Symbolic limit at infinity: lim_{var -> +inf} f(var) (dir >= 0) or
// lim_{var -> -inf} f(var) (dir < 0).
LimitResult limitAtInfinity(Ctx &c, Expr f, Expr var, int dir = +1,
                            Budget *budget = nullptr);

struct SymSumResult
{
    enum class Status
    {
        Unevaluated,
        ProvedSymbolic,
        Divergent,
    };

    Status status = Status::Unevaluated;
    Expr value;    // closed-form sum when status == ProvedSymbolic
    Expr antidiff; // discrete antidifference G(var) with G(var + 1) - G(var) == f(var) when applicable
    std::string reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Symbolic finite and infinite summation sum_{var = a}^{b} f(var):
//   1. Faulhaber-Bernoulli polynomial summation for arbitrary degree polynomials P(var).
//   2. Geometric and arithmetico-geometric summation sum P(var) * r^(c1*var + c0)
//      via upper-triangular finite-difference back-substitution.
//   3. Rational partial-fraction / Gosper integer-shift telescoping.
//   4. Classical infinite series (b = inf/oo/infinity): Euler-Riemann zeta(2m),
//      Dirichlet alternating eta(2m), alternating harmonic / Gregory-Leibniz,
//      and exponential factorial series sum P(var)*x^var/factorial(var).
//   5. Certified by finite-difference identity G(var + 1) - G(var) == f(var)
//      for antidifference-backed sums.
SymSumResult symsum(Ctx &c, Expr f, Expr var, Expr a, Expr b,
                    Budget *budget = nullptr);

} // namespace numkit::cas
