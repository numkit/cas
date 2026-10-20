// ode/dsolve.hpp — certified symbolic solver for 1st- and 2nd-order ODEs.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>

#include <string>
#include <vector>

namespace numkit::cas {

struct OdeResult
{
    enum class Status
    {
        Unevaluated,
        Proved,
    };

    Status status = Status::Unevaluated;
    Expr y; // explicit solution y(x), certified by substituting into the ODE
    std::string reason;

    bool proved() const { return status == Status::Proved; }
};

// Solve a 1st-order ODE `y'(x) = rhs(x, y)` for `y(x)` (with integration
// constant symbol `"C1"`):
//   1. Direct quadrature: y' = f(x)
//   2. Linear 1st-order:  y' = A(x)*y + B(x) (integrating factor)
//   3. Separable:         y' = g(x)*h(y)
//   4. Bernoulli:         y' = A(x)*y + B(x)*y^n
// Every candidate solution is certified by checking `simplify(d(y)/dx - rhs(x, y)) == 0`.
OdeResult dsolve1(Ctx &c, Expr rhs, Expr x, Expr y,
                  Budget *budget = nullptr);

// Solve a 1st-order Initial Value Problem `y'(x) = rhs(x, y), y(x0) = y0`,
// certifying both the ODE identity and the initial condition `y(x0) == y0`.
OdeResult dsolve1IVP(Ctx &c, Expr rhs, Expr x, Expr y, Expr x0, Expr y0,
                     Budget *budget = nullptr);

// Solve a 2nd-order constant-coefficient linear ODE:
//   a * y''(x) + b * y'(x) + d * y(x) = f(x)
// with integration constants `"C1"` and `"C2"`:
//   - Overdamped (disc > 0), critically damped (disc == 0), and oscillatory
//     underdamped (disc < 0 -> real exp*cos/sin form) homogeneous bases;
//   - Particular solution y_p(x) for polynomial, exponential, and
//     trigonometric forcing terms f(x) (including resonance) via undetermined
//     coefficients (`SymMatrix` + `linsolve`) and Variation of Parameters.
// Certified by checking `simplify(a*y'' + b*y' + d*y - f) == 0`.
OdeResult dsolve2Linear(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                        Budget *budget = nullptr);

// Solve a 2nd-order constant-coefficient linear IVP:
//   a * y''(x) + b * y'(x) + d * y(x) = f(x),  y(x0) = y0,  y'(x0) = dy0
// Certified against the ODE and both initial conditions.
OdeResult dsolve2LinearIVP(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                           Expr x0, Expr y0, Expr dy0,
                           Budget *budget = nullptr);

struct OdeSystemResult
{
    enum class Status
    {
        Unevaluated,
        Proved,
    };

    Status status = Status::Unevaluated;
    std::vector<Expr> y;   // n components [y_0(x), ..., y_{n-1}(x)]
    SymMatrix fundamental; // n x n fundamental matrix Phi(x) = exp(A*x) with Phi(0) = I
    std::string reason;

    bool proved() const { return status == Status::Proved; }
};

// Solve a 1st-order constant-coefficient linear ODE system:
//   y'(x) = A * y(x)   (or y'(x) = A * y(x) + f(x))
// with integration constants "C1", ..., "Cn" (where C_i = y_i(0) for the
// homogeneous system). Supports distinct real eigenvalues, repeated/defective
// eigenvalues (Jordan blocks), complex-conjugate pairs alpha +- i*w ->
// exp(alpha*x)*cos(w*x), exp(alpha*x)*sin(w*x), and inhomogeneous forcing f(x)
// via Variation of Parameters.
// Certified by verifying simplify(y'_i(x) - (A*y(x) + f(x))_i) == 0 for all i.
OdeSystemResult dsolveSystem1Linear(Ctx &c, const SymMatrix &A, Expr x,
                                    Budget *budget = nullptr);
OdeSystemResult dsolveSystem1Linear(Ctx &c, const SymMatrix &A,
                                    const std::vector<Expr> &f, Expr x,
                                    Budget *budget = nullptr);

// Solve a 1st-order constant-coefficient linear ODE system Initial Value Problem:
//   y'(x) = A * y(x) (+ f(x)),   y(x0) = y0
// Certified against the ODE system and all n initial conditions y_i(x0) == y0_i.
OdeSystemResult dsolveSystem1LinearIVP(Ctx &c, const SymMatrix &A, Expr x,
                                       Expr x0, const std::vector<Expr> &y0,
                                       Budget *budget = nullptr);
OdeSystemResult dsolveSystem1LinearIVP(Ctx &c, const SymMatrix &A,
                                       const std::vector<Expr> &f, Expr x,
                                       Expr x0, const std::vector<Expr> &y0,
                                       Budget *budget = nullptr);

} // namespace numkit::cas
