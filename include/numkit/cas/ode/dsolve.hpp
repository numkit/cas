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
//   5. Homogeneous:       y' = F(y / x) (substitution y = u * x)
//   6. Exact / integrating factor: M(x, y)*dx + N(x, y)*dy = 0 with mu(x) or mu(y)
//   7. Riccati:           y' = q0(x) + q1(x)*y + q2(x)*y^2 (automatic particular solution
//                         search or 2nd-order linear / Euler-Cauchy reduction)
// Every candidate solution is certified by checking `simplify(d(y)/dx - rhs(x, y)) == 0`.
OdeResult dsolve1(Ctx &c, Expr rhs, Expr x, Expr y,
                  Budget *budget = nullptr);

// Solve a 1st-order Riccati ODE `y'(x) = rhs(x, y) = q0(x) + q1(x)*y + q2(x)*y^2`
// given a known particular solution `yPart(x)` (or null `yPart` to search
// automatically), reducing via `y = yPart + 1/u` to a linear 1st-order ODE for `u(x)`
// and certifying `simplify(d(y)/dx - rhs(x, y)) == 0`.
OdeResult dsolve1Riccati(Ctx &c, Expr rhs, Expr x, Expr y,
                         Expr yPart = Expr{}, Budget *budget = nullptr);

struct ClairautResult
{
    enum class Status { Unevaluated, Proved };

    Status status = Status::Unevaluated;
    Expr general;  // general linear family y(x) = C1 * x + g(C1)
    Expr singular; // singular envelope solution (if x + g'(p) = 0 is solvable; null otherwise)
    std::string reason;

    bool proved() const { return status == Status::Proved; }
};

// Solve a 1st-order Clairaut ODE `y(x) = x * y'(x) + g(y'(x))` where `gOfP`
// is the expression `g(p)` in symbol `p = y'(x)`:
//   - constructs and certifies the general linear family `y(x) = C1 * x + g(C1)`;
//   - solves `x + g'(p) = 0` for `p(x)` to construct and certify the singular
//     envelope solution when it exists.
ClairautResult dsolve1Clairaut(Ctx &c, Expr gOfP, Expr x, Expr p,
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

// Solve a 2nd-order Euler-Cauchy equidimensional linear ODE:
//   a * x^2 * y''(x) + b * x * y'(x) + d * y(x) = f(x)
// with integration constants "C1" and "C2":
//   - Distinct real indicial roots r1, r2 -> x^r1, x^r2;
//   - Repeated indicial root r -> x^r, x^r * log(x);
//   - Complex-conjugate indicial roots alpha +- i*w -> x^alpha*cos(w*log(x)), x^alpha*sin(w*log(x));
//   - Inhomogeneous forcing f(x) via Variation of Parameters and x = exp(t) reduction.
// Certified by checking `simplify(a*x^2*y'' + b*x*y' + d*y - f) == 0`.
OdeResult dsolve2EulerCauchy(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                             Budget *budget = nullptr);

// Solve a 2nd-order Euler-Cauchy Initial Value Problem:
//   a * x^2 * y''(x) + b * x * y'(x) + d * y(x) = f(x),  y(x0) = y0,  y'(x0) = dy0
// Certified against the ODE and both initial conditions.
OdeResult dsolve2EulerCauchyIVP(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                                Expr x0, Expr y0, Expr dy0,
                                Budget *budget = nullptr);

// Solve an N-th order constant-coefficient linear ODE (N >= 1):
//   coeffs[N] * y^(N)(x) + coeffs[N-1] * y^(N-1)(x) + ... + coeffs[0] * y(x) = f(x)
// where `coeffs = {a_0, a_1, ..., a_N}` (from y(x) up to y^(N)(x), with a_N != 0)
// using integration constants "C1", ..., "CN".
// Certified by verifying `simplify(sum_{k=0}^N coeffs[k] * y^(k)(x) - f(x)) == 0`.
OdeResult dsolveNLinear(Ctx &c, const std::vector<Expr> &coeffs, Expr f,
                        Expr x, Budget *budget = nullptr);

// Solve an N-th order constant-coefficient linear IVP:
//   sum_{k=0}^N coeffs[k] * y^(k)(x) = f(x),
//   y(x0) = initVals[0], y'(x0) = initVals[1], ..., y^(N-1)(x0) = initVals[N-1].
// Certified against the ODE and all N initial conditions.
OdeResult dsolveNLinearIVP(Ctx &c, const std::vector<Expr> &coeffs, Expr f,
                           Expr x, Expr x0, const std::vector<Expr> &initVals,
                           Budget *budget = nullptr);

// Solve a 2nd-order nonlinear ODE `y''(x) = rhs(x, y, dy)` (where `dy` is the
// symbol representing `y'(x)`) via exact order reduction with integration
// constants "C1" and "C2":
//   - Dependent variable y missing (`rhs = F(x, y')`): substitution `p(x) = y'(x)`
//     reduces to 1st-order ODE `p'(x) = F(x, p)` followed by quadrature `y = int p dx + C2`;
//   - Independent variable x missing / autonomous (`rhs = F(y, y')`): substitution
//     `y' = p(y), y'' = p * dp/dy` reduces to `dp/dy = F(y, p) / p` followed by
//     separable integration `int dy / p(y) = x + C2`.
// Certified by verifying `simplify(y''(x) - rhs(x, y(x), y'(x))) == 0`.
OdeResult dsolve2Nonlinear(Ctx &c, Expr rhs, Expr x, Expr y, Expr dy,
                           Budget *budget = nullptr);

// Solve a 2nd-order nonlinear Initial Value Problem:
//   y''(x) = rhs(x, y, dy),  y(x0) = y0,  y'(x0) = dy0
// Certified against the ODE and both initial conditions `y(x0) == y0`, `y'(x0) == dy0`.
OdeResult dsolve2NonlinearIVP(Ctx &c, Expr rhs, Expr x, Expr y, Expr dy,
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
