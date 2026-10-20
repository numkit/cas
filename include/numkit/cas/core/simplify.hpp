// core/simplify.hpp — cost-guided algebraic and transcendental simplification.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

namespace numkit::cas {

// Simplify an expression `e` by combining rational normal forms (common
// denominator + polynomial GCD cancellation), polynomial expansion and
// factorization, Pythagorean/hyperbolic trigonometric identities, inverse
// function cancellations, and exponential/logarithmic laws, selecting the
// canonical form that minimizes `(Ctx::exprCost, Ctx::leafCount)`.
Expr simplify(Ctx &c, Expr e, Budget *budget = nullptr);

} // namespace numkit::cas
