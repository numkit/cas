// core/simplify.hpp — cost-guided algebraic and transcendental simplification.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <string>
#include <vector>

namespace numkit::cas {

// Simplify an expression `e` by combining rational normal forms (common
// denominator + polynomial GCD cancellation), polynomial expansion and
// factorization, Pythagorean/hyperbolic trigonometric identities, inverse
// function cancellations, and exponential/logarithmic laws, selecting the
// canonical form that minimizes `(Ctx::exprCost, Ctx::leafCount)`.
Expr simplify(Ctx &c, Expr e, Budget *budget = nullptr);

// ---------------------------------------------------------------------------
// MATLAB Symbolic Math Toolbox Scripting-Surface Utilities (Item 77)
// ---------------------------------------------------------------------------

struct NumDenResult
{
    Expr num; // numerator expression
    Expr den; // denominator expression (normalized so den == 1 for polynomial/non-rational expressions)
};

// Extract the canonical rational numerator and denominator of `e` (equivalent
// to MATLAB `[N, D] = numden(e)`), certified by `simplify(num / den - e) == 0`.
NumDenResult numden(Ctx &c, Expr e, Budget *budget = nullptr);

struct PolyCoeffsResult
{
    std::vector<Expr> coefficients; // non-zero coefficients in ascending power order (MATLAB `[c, t] = coeffs(p, x)`)
    std::vector<Expr> terms;        // corresponding monomials `var^k`
    std::vector<Expr> dense;        // dense coefficient vector `[c_0, c_1, ..., c_d]` from degree 0 to d
};

// Extract polynomial coefficients and monomial terms of `e` with respect to
// `var` (supporting symbolic coefficients in other variables).
PolyCoeffsResult coeffs(Ctx &c, Expr e, Expr var);

// Collect terms of `e` with respect to powers of `var`:
//   sum_k simplify(c_k) * var^k,
// certified by `simplify(expand(result - e)) == 0`.
Expr collect(Ctx &c, Expr e, Expr var);

// Partial fraction decomposition of a rational function `e` in `var` over Q:
//   e(var) = Q(var) + sum_{i} sum_{k=1}^{m_i} r_{i,k}(var) / P_i(var)^k
// where each `P_i` is monic irreducible over Q and `deg(r_{i,k}) < deg(P_i)`,
// certified by `simplify(result - e) == 0`.
Expr partfrac(Ctx &c, Expr e, Expr var, Budget *budget = nullptr);

// Render `e` as publication-ready LaTeX math (`\frac`, `\sqrt`, Greek symbols,
// trigonometric/special functions).
std::string toLatex(const Ctx &c, Expr e);

inline std::string latex(const Ctx &c, Expr e) { return toLatex(c, e); }

// Render `e` as valid C/C++ floating-point expression code (`std::pow`,
// `std::sqrt`, `std::sin`, `std::cos`, `std::tgamma`, etc.).
std::string toCCode(const Ctx &c, Expr e);

inline std::string ccode(const Ctx &c, Expr e) { return toCCode(c, e); }

} // namespace numkit::cas
