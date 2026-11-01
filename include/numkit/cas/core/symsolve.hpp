// core/symsolve.hpp — symbolic equation and polynomial system solver.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <utility>
#include <vector>

namespace numkit::cas {

// Solve a symbolic equation `eqn == 0` for `var`, returning distinct
// symbolic solutions `var = r_i`:
//   1. Single-occurrence invertible algebraic and transcendental equations
//      (linear/power/exp/log/trig/hyperbolic peel).
//   2. Parametric symbolic polynomials in `var` (linear, quadratic in
//      radicals, biquadratic degree 4, binomial/monomial powers `a*x^n + b = 0`,
//      and factored products).
//   3. Univariate polynomials over Q[x] via Zassenhaus factorization
//      (`factorOverQ`), emitting exact rationals, quadratic radicals, and
//      canonical `RootOf` atoms for irreducible factors of degree >= 3.
// Every candidate root is checked against denominator poles of `eqn`.
std::vector<Expr> solveSymbolic(Ctx &c, Expr eqn, Expr var,
                                Budget *budget = nullptr);

// Solve a system of two algebraic equations `eq1 == 0, eq2 == 0` in two
// variables `(x, y)` via the Sylvester resultant `det(Sylv_y(eq1, eq2))`
// over `SymMatrix`, back-substitution, and symbolic residual verification.
std::vector<std::pair<Expr, Expr>> solveSystem2(Ctx &c, Expr eq1, Expr eq2,
                                                Expr x, Expr y,
                                                Budget *budget = nullptr);

// Solve a system of nonlinear polynomial/rational equations `eqs[i] == 0`
// for `vars = {x_0, ..., x_{k-1}}`, returning all distinct certified solution
// tuples `{r_0, ..., r_{k-1}}`:
//   1. Lexicographic Groebner basis triangular elimination over Q[x_0, ..., x_{k-1}]
//      followed by recursive back-substitution via `solveSymbolic`.
//   2. Parametric linear/substitution peel and 2-variable Sylvester resultant
//      fallback when symbolic parameters outside `vars` are present.
// Every returned tuple is certified by verifying `simplify(subs(eqs[i])) == 0`
// and absence of denominator poles for all equations.
std::vector<std::vector<Expr>> solveSystem(Ctx &c,
                                           const std::vector<Expr> &eqs,
                                           const std::vector<Expr> &vars,
                                           Budget *budget = nullptr);

} // namespace numkit::cas
