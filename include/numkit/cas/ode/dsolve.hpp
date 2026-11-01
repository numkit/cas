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

// Solve a 2nd-order variable-coefficient special-function linear ODE:
//   a(x) * y''(x) + b(x) * y'(x) + d(x) * y(x) = f(x)
// with integration constants "C1" and "C2", covering:
//   - Airy and shifted/scaled Airy ODEs: y'' - k*(x - x0)*y = 0 -> airyAi, airyBi;
//   - Bessel, Modified Bessel, and Lommel/spherical Bessel ODEs:
//       x^2*y'' + p0*x*y' + (A*x^2 + C)*y = 0 -> x^((1-p0)/2) * (C1*J_nu(w*x) + C2*Y_nu(w*x))
//       or x^((1-p0)/2) * (C1*I_nu(w*x) + C2*K_nu(w*x));
//   - Legendre's ODE: (1 - x^2)*y'' - 2*x*y' + n*(n + 1)*y = 0 -> legendreP(n, x) (+ Q_n(x));
//   - Chebyshev's 1st & 2nd kind ODEs:
//       (1 - x^2)*y'' - x*y' + n^2*y = 0 -> C1*chebyshevT(n, x) + C2*sqrt(1 - x^2)*chebyshevU(n - 1, x),
//       (1 - x^2)*y'' - 3*x*y' + n*(n + 2)*y = 0 -> C1*chebyshevU(n, x) + C2*(1 - x^2)^(-1/2)*chebyshevT(n + 1, x);
//   - Hermite's ODE: y'' - 2*x*y' + 2*n*y = 0 -> hermiteH(n, x) (+ erfi second branch);
//   - Laguerre's ODE: x*y'' + (1 - x)*y' + n*y = 0 -> laguerreL(n, x) (+ Ei second branch);
//   - Liouville reduction of order and Variation of Parameters / Undetermined Coefficients
//     for inhomogeneous forcing f(x).
// Certified by verifying `simplify(a*y'' + b*y' + d*y - f) == 0`.
OdeResult dsolve2Special(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                         Budget *budget = nullptr);

// Solve a 2nd-order variable-coefficient special-function linear IVP:
//   a(x) * y''(x) + b(x) * y'(x) + d(x) * y(x) = f(x),  y(x0) = y0,  y'(x0) = dy0
// Certified against the ODE and both initial conditions.
OdeResult dsolve2SpecialIVP(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                            Expr x0, Expr y0, Expr dy0,
                            Budget *budget = nullptr);

// Solve a 2nd-order variable-coefficient linear ODE via certified Taylor or
// Frobenius power series expansion around `x0` up to degree `order`:
//   a(x) * y''(x) + b(x) * y'(x) + d(x) * y(x) = f(x)
// - At an ordinary point `x0` (`a(x0) != 0`), constructs the general truncated
//   Taylor series with integration constants `C1 = y(x0)` and `C2 = y'(x0)`,
//   certified by verifying `taylor(a*y'' + b*y' + d*y - f, x, x0, order - 2) == 0`.
// - At a regular singular point `x0` (`a(x0) == 0`, `f == 0`), solves the indicial
//   equation `r*(r - 1) + p0*r + q0 = 0` and constructs certified Frobenius series
//   branches `(x - x0)^r * sum_{k=0}^{order} c_k * (x - x0)^k`.
OdeResult dsolveSeries(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                       Expr x0, int order = 6, Budget *budget = nullptr);

// Solve a 2nd-order variable-coefficient linear Initial Value Problem via
// certified Taylor power series around an ordinary point `x0` up to degree `order`:
//   a(x) * y''(x) + b(x) * y'(x) + d(x) * y(x) = f(x),  y(x0) = y0,  y'(x0) = dy0
// Certified by verifying `taylor(a*y'' + b*y' + d*y - f, x, x0, order - 2) == 0`,
// `y(x0) == y0`, and `y'(x0) == dy0`.
OdeResult dsolveSeriesIVP(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                          Expr x0, Expr y0, Expr dy0, int order = 6,
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
