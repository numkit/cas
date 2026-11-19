// linalg/symmatrix.hpp — symbolic matrices, multivariable calculus, and exact linear algebra.
#pragma once

#include <keel/array.h>
#include <keel/core.h>
#include <keel/string.h>
#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <cstddef>

namespace numkit::cas {

// Dense symbolic matrix over hash-consed `Expr` nodes.
class SymMatrix
{
public:
    SymMatrix() noexcept = default;
    SymMatrix(const SymMatrix &o)
        : rows_(o.rows_), cols_(o.cols_), data_(o.data_.clone())
    {
    }
    SymMatrix &operator=(const SymMatrix &o)
    {
        if (this != &o) {
            rows_ = o.rows_;
            cols_ = o.cols_;
            data_ = o.data_.clone();
        }
        return *this;
    }
    SymMatrix(SymMatrix &&) noexcept = default;
    SymMatrix &operator=(SymMatrix &&) noexcept = default;

    SymMatrix(keel::usize rows, keel::usize cols, Expr fill = Expr{});
    SymMatrix(keel::usize rows, keel::usize cols, keel::Array<Expr> entries);

    static SymMatrix zeros(Ctx &c, keel::usize rows, keel::usize cols);
    static SymMatrix eye(Ctx &c, keel::usize n);
    static SymMatrix diag(Ctx &c, keel::ArrayRef<Expr> d);
    static SymMatrix column(keel::ArrayRef<Expr> v);
    static SymMatrix row(keel::ArrayRef<Expr> v);

    keel::usize rows() const { return rows_; }
    keel::usize cols() const { return cols_; }
    bool empty() const { return rows_ == 0 || cols_ == 0; }
    bool isSquare() const { return rows_ == cols_; }

    Expr &at(keel::usize r, keel::usize c)
    {
        return data_[r * cols_ + c];
    }
    const Expr &at(keel::usize r, keel::usize c) const
    {
        return data_[r * cols_ + c];
    }
    Expr &operator()(keel::usize r, keel::usize c) { return at(r, c); }
    const Expr &operator()(keel::usize r, keel::usize c) const { return at(r, c); }

    const keel::Array<Expr> &data() const { return data_; }

    // Structural matrix operations
    SymMatrix transpose() const;
    SymMatrix add(Ctx &c, const SymMatrix &other) const;
    SymMatrix sub(Ctx &c, const SymMatrix &other) const;
    SymMatrix mul(Ctx &c, const SymMatrix &other) const;
    SymMatrix scale(Ctx &c, Expr scalar) const;

    // Elementwise symbolic operations
    SymMatrix expand(Ctx &c) const;
    SymMatrix diff(Ctx &c, Expr var) const;
    SymMatrix subs(Ctx &c, Expr from, Expr to) const;

    // Trace of a square matrix (returns null Expr if not square)
    Expr trace(Ctx &c) const;

    // Readable MATLAB-style bracket representation: "[a, b; c, d]"
    keel::String toString(const Ctx &c) const;

private:
    keel::usize rows_ = 0;
    keel::usize cols_ = 0;
    keel::Array<Expr> data_;
};

// Normalize a rational symbolic expression by combining sums of fractions
// over a common denominator, expanding polynomial numerators/denominators,
// and canceling univariate polynomial GCDs over Q[x] when applicable.
Expr simplifyRationalExpr(Ctx &c, Expr e);

// Multivariable vector calculus (MATLAB Symbolic Math Toolbox conventions):
//   - jacobian(c, funcs, vars):   m x n matrix J(i, j) = df_i / dx_j
//   - gradient(c, f, vars):       n x 1 column vector grad(i, 0) = df / dx_i
//   - hessian(c, f, vars):        n x n symmetric matrix H(i, j) = d^2f / (dx_i dx_j)
//   - divergence(c, F, vars):     scalar sum_{i=0}^{n-1} dF_i / dx_i
//   - curl(c, F, vars):           3 x 1 column vector nabla x F (3D vector field)
//   - laplacian(c, f, vars):      scalar sum_{i=0}^{n-1} d^2f / dx_i^2
SymMatrix jacobian(Ctx &c, keel::ArrayRef<Expr> funcs,
                   keel::ArrayRef<Expr> vars);
SymMatrix gradient(Ctx &c, Expr f, keel::ArrayRef<Expr> vars);
SymMatrix hessian(Ctx &c, Expr f, keel::ArrayRef<Expr> vars);
Expr divergence(Ctx &c, keel::ArrayRef<Expr> F,
                keel::ArrayRef<Expr> vars);
SymMatrix curl(Ctx &c, keel::ArrayRef<Expr> F,
               keel::ArrayRef<Expr> vars);
Expr laplacian(Ctx &c, Expr f, keel::ArrayRef<Expr> vars);

// Construct the n x n Wronskian matrix W(i, j) = d^i f_j / d(var)^i (0 <= i, j < n)
// and its exact determinant wronskian(c, funcs, var).
SymMatrix wronskianMatrix(Ctx &c, keel::ArrayRef<Expr> funcs, Expr var);
Expr wronskian(Ctx &c, keel::ArrayRef<Expr> funcs, Expr var,
               Budget *budget = nullptr);

struct PotentialResult
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    Expr phi; // scalar potential phi(vars) satisfying gradient(c, phi, vars) == F
    keel::String reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Reconstruct a scalar potential `phi` for a conservative vector field `F`
// in `vars` (`nabla phi == F`), checking curl-free integrability conditions
// `dF_i/dx_j == dF_j/dx_i` and certifying `gradient(c, phi, vars) == F`.
PotentialResult scalarPotential(Ctx &c, keel::ArrayRef<Expr> F,
                                keel::ArrayRef<Expr> vars,
                                Budget *budget = nullptr);

// Characteristic polynomial det(lambda * I - A) and adjugate matrix via
// the division-free Faddeev-LeVerrier recurrence over Q(x).
// `charpoly` returns a polynomial in `lambda` (or null Expr if A is not square).
Expr charpoly(Ctx &c, const SymMatrix &A, Expr lambda,
              Budget *budget = nullptr);

// Adjugate (classical adjoint) matrix adj(A) satisfying A * adj(A) = det(A) * I.
SymMatrix adjugate(Ctx &c, const SymMatrix &A, Budget *budget = nullptr);

// Exact determinant of a square symbolic matrix A.
Expr det(Ctx &c, const SymMatrix &A, Budget *budget = nullptr);

// Exact inverse A^(-1) of a non-singular square symbolic matrix A.
// Returns an empty (0x0) SymMatrix if A is singular or non-square.
SymMatrix inv(Ctx &c, const SymMatrix &A, Budget *budget = nullptr);

// Solve the symbolic linear system A * X = B for X (where A is m x n and
// B is m x k) using exact Gaussian elimination with rational normalization.
// Returns an empty (0x0) SymMatrix if the system is inconsistent or
// underdetermined (rank < n).
SymMatrix linsolve(Ctx &c, const SymMatrix &A, const SymMatrix &B,
                   Budget *budget = nullptr);

// Compute an exact basis of the nullspace (kernel) ker(A) = { v : A * v = 0 }
// via symbolic Gauss-Jordan elimination to Reduced Row Echelon Form (RREF).
// Returns a vector of n x 1 column matrices spanning ker(A) (empty if rank(A) == n).
keel::Array<SymMatrix> nullspace(Ctx &c, const SymMatrix &A,
                                 Budget *budget = nullptr);

struct EigenPair
{
    Expr lambda;                    // eigenvalue
    keel::usize multiplicity = 1;   // algebraic multiplicity in charpoly(A)
    keel::Array<SymMatrix> vectors; // geometric eigenspace basis: n x 1 columns v with (A - lambda*I)*v = 0
};

// Compute the symbolic/real eigenvalues of a square matrix A (roots of
// charpoly(A, lambda) = 0), repeated according to their algebraic multiplicity.
keel::Array<Expr> eigenvalues(Ctx &c, const SymMatrix &A,
                              Budget *budget = nullptr);

// Compute the eigenpairs (lambda, algebraic multiplicity, basis of ker(A - lambda*I))
// of a square matrix A.
keel::Array<EigenPair> eigenvectors(Ctx &c, const SymMatrix &A,
                                    Budget *budget = nullptr);

// Compute the exact matrix exponential exp(A * t) of a square matrix A
// (with respect to scalar parameter t, where A is independent of t) via
// Laplace resolvent inversion L^{-1}{(s*I - A)^(-1)}(t) and spectral/Putzer
// fallback, certified by verifying d/dt Phi(t) == A * Phi(t) and Phi(0) == I.
// Returns an empty (0x0) SymMatrix if A is non-square or cannot be exponentiated.
SymMatrix matrixExp(Ctx &c, const SymMatrix &A, Expr t,
                    Budget *budget = nullptr);

// Compute the exact Reduced Row Echelon Form (RREF) of an m x n matrix A
// via Gauss-Jordan elimination. Optionally populates `pivotColsOut` with the
// 0-based indices of the pivot columns. Returns an empty (0x0) SymMatrix if
// the budget is exhausted.
SymMatrix rref(Ctx &c, const SymMatrix &A,
               keel::Array<keel::usize> *pivotColsOut = nullptr,
               Budget *budget = nullptr);

// Compute the exact rank of an m x n symbolic matrix A (number of pivot
// columns in its RREF; 0 for an empty matrix).
keel::usize rank(Ctx &c, const SymMatrix &A, Budget *budget = nullptr);

struct LUDecomposition
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    SymMatrix L;                    // m x m unit lower-triangular matrix (L(i, i) == 1)
    SymMatrix U;                    // m x n upper-triangular (row-echelon) matrix
    SymMatrix P;                    // m x m row-permutation matrix: P * A == L * U
    keel::Array<keel::usize> perm;  // row permutation indices (P(i, perm[i]) == 1)
    int sign = 1;                   // determinant sign of P (+1 or -1)
    keel::String reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Compute the exact pivoted LU decomposition P * A = L * U of an m x n
// symbolic matrix A, certified by verifying P * A == L * U, unit lower-
// triangularity of L, and upper-triangularity of U.
LUDecomposition lu(Ctx &c, const SymMatrix &A, Budget *budget = nullptr);

// Perform exact Gram-Schmidt orthogonalization (or orthonormalization when
// `normalize == true`) on a sequence of m x 1 column vectors, dropping any
// vector that lies in the span of previous vectors.
keel::Array<SymMatrix> gramSchmidt(Ctx &c,
                                   keel::ArrayRef<SymMatrix> cols,
                                   bool normalize = true,
                                   Budget *budget = nullptr);

struct QRDecomposition
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    SymMatrix Q; // m x n column-orthonormal matrix (Q^T * Q == I_n)
    SymMatrix R; // n x n upper-triangular matrix: A == Q * R
    keel::String reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Compute the exact thin QR decomposition A = Q * R of an m x n matrix A
// (with m >= n and linearly independent columns), certified by verifying
// Q * R == A, Q^T * Q == I_n, and upper-triangularity of R.
QRDecomposition qr(Ctx &c, const SymMatrix &A, Budget *budget = nullptr);

struct JordanDecomposition
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    SymMatrix J;    // n x n block-diagonal Jordan canonical form
    SymMatrix P;    // n x n invertible similarity matrix: A * P == P * J
    SymMatrix PInv; // n x n exact inverse P^(-1): J == P^(-1) * A * P
    keel::String reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Compute the exact Jordan canonical form A = P * J * P^(-1) of a square
// matrix A whose eigenvalues lie in the solvable symbolic/radical domain,
// certified by verifying A * P == P * J and P * PInv == I_n.
JordanDecomposition jordanForm(Ctx &c, const SymMatrix &A,
                               Budget *budget = nullptr);

struct ExtremumPoint
{
    enum class Classification
    {
        Unknown,
        LocalMinimum,
        LocalMaximum,
        SaddlePoint,
    };

    keel::Array<Expr> point;       // stationary point (x_0*, ..., x_{n-1}*)
    keel::Array<Expr> multipliers; // Lagrange multipliers (lambda_0*, ..., lambda_{m-1}*)
    Expr value;                    // objective value f(x*)
    Classification kind = Classification::Unknown;
};

struct LagrangeExtremaResult
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    keel::Array<ExtremumPoint> points;
    bool certified = false;
    keel::String reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Symbolic unconstrained and Lagrange-multiplier constrained stationary/extremum
// solver for objective `f(vars)` subject to equality constraints `g_j(vars) = 0`:
//   1. Forms the Lagrangian L(vars, lambda) = f(vars) - sum_j lambda_j * g_j(vars).
//   2. Solves the KKT stationarity and feasibility system
//        dL/dx_i = 0 (0 <= i < n),  g_j(x) = 0 (0 <= j < m)
//      via `solveSystem` (Lex Groebner basis + back-substitution).
//   3. Certifies every candidate solution (x*, lambda*) by substituting into
//      all KKT equations and verifying zero residuals, evaluates f(x*), and
//      classifies critical points via Hessian / bordered Hessian principal minors.
LagrangeExtremaResult lagrangeExtrema(
    Ctx &c, Expr f, keel::ArrayRef<Expr> vars,
    keel::ArrayRef<Expr> constraints = {},
    Budget *budget = nullptr);

// Canonical Poisson bracket of two phase-space observables f(q, p) and g(q, p):
//   {f, g}_{q, p} = sum_{i=0}^{n-1} (df/dq_i * dg/dp_i - df/dp_i * dg/dq_i)
Expr poissonBracket(Ctx &c, Expr f, Expr g, keel::ArrayRef<Expr> q,
                    keel::ArrayRef<Expr> p);

inline Expr poissonBracket(Ctx &c, Expr f, Expr g, Expr q, Expr p)
{
    return poissonBracket(c, f, g, keel::ArrayRef<Expr>(&q, 1),
                          keel::ArrayRef<Expr>(&p, 1));
}

struct VariationalField
{
    Expr q;                        // generalized coordinate / field variable q_i(t)
    keel::Array<Expr> derivatives; // ordered time-derivative symbols [q'_i, q''_i, ..., q^{(k)}_i]
};

struct EulerLagrangeResult
{
    keel::Array<Expr> equations;        // E_i(L) = dL/dq_i - d/dt(dL/dq'_i) + d^2/dt^2(dL/dq''_i) - ...
    keel::Array<Expr> momenta;          // canonical momenta p_i = dL/dq'_i
    Expr energy;                        // Beltrami energy function E = sum_i q'_i * dL/dq'_i - L
    keel::Array<Expr> cyclicCoords;     // ignorable coordinates q_i with dL/dq_i == 0
    keel::Array<Expr> conservedMomenta; // conserved momenta p_i for each cyclic coordinate
    bool autonomous = false;            // true when dL/dt == 0
};

// Calculus of variations: Euler-Lagrange (and higher-order Euler-Poisson)
// equations for Lagrangian L(t, q_i, q'_i, q''_i, ...):
//   E_i(L) = dL/dq_i + sum_{k>=1} (-1)^k d^k/dt^k (dL / dq_i^{(k)}) = 0.
EulerLagrangeResult eulerLagrange(Ctx &c, Expr L, Expr t,
                                  keel::ArrayRef<VariationalField> fields);

EulerLagrangeResult eulerLagrange(Ctx &c, Expr L, Expr t,
                                  keel::ArrayRef<Expr> q,
                                  keel::ArrayRef<Expr> dq,
                                  keel::ArrayRef<Expr> ddq = {});

inline EulerLagrangeResult eulerLagrange(Ctx &c, Expr L, Expr t, Expr q,
                                         Expr dq, Expr ddq = Expr{})
{
    return eulerLagrange(c, L, t, keel::ArrayRef<Expr>(&q, 1),
                         keel::ArrayRef<Expr>(&dq, 1),
                         ddq.isNull() ? keel::ArrayRef<Expr>{}
                                      : keel::ArrayRef<Expr>(&ddq, 1));
}

struct HamiltonEquationsResult
{
    Expr H;                      // Hamiltonian H(t, q, p)
    keel::Array<Expr> dqdt;      // canonical coordinate rates q'_i =  dH/dp_i == {q_i, H}
    keel::Array<Expr> dpdt;      // canonical momentum rates   p'_i = -dH/dq_i == {p_i, H}
    keel::Array<Expr> qDotFromP; // inverse velocity map q'_i(q, p) (when obtained via Legendre transform)
    bool certified = false;
    keel::String reason;
};

// Canonical Hamilton equations for Hamiltonian H(t, q, p):
//   q'_i = dH/dp_i = {q_i, H},   p'_i = -dH/dq_i = {p_i, H}.
HamiltonEquationsResult hamiltonEquations(Ctx &c, Expr H,
                                          keel::ArrayRef<Expr> q,
                                          keel::ArrayRef<Expr> p);

inline HamiltonEquationsResult hamiltonEquations(Ctx &c, Expr H, Expr q, Expr p)
{
    return hamiltonEquations(c, H, keel::ArrayRef<Expr>(&q, 1),
                             keel::ArrayRef<Expr>(&p, 1));
}

// Legendre transformation from Lagrangian L(t, q, dq) to Hamiltonian H(t, q, p)
// and canonical Hamilton equations:
//   1. Solves p_i = dL/d(dq_i) for velocities dq_i(q, p).
//   2. Evaluates H(t, q, p) = sum_i p_i * dq_i(q, p) - L(t, q, dq(q, p)).
//   3. Computes canonical equations dqdt_i = dH/dp_i, dpdt_i = -dH/dq_i and
//      certifies the Legendre involution dH/dp_i == dq_i(q, p).
HamiltonEquationsResult legendreTransform(Ctx &c, Expr L,
                                          keel::ArrayRef<Expr> q,
                                          keel::ArrayRef<Expr> dq,
                                          keel::ArrayRef<Expr> p,
                                          Budget *budget = nullptr);

inline HamiltonEquationsResult legendreTransform(Ctx &c, Expr L, Expr q,
                                                 Expr dq, Expr p,
                                                 Budget *budget = nullptr)
{
    return legendreTransform(c, L, keel::ArrayRef<Expr>(&q, 1),
                             keel::ArrayRef<Expr>(&dq, 1),
                             keel::ArrayRef<Expr>(&p, 1), budget);
}

// ---------------------------------------------------------------------------
// Differential Geometry of Curves/Surfaces & Riemannian Geometry (Item 76)
// ---------------------------------------------------------------------------

struct FrenetSerretResult
{
    keel::Array<Expr> T; // unit tangent vector T(t) = r'(t) / ||r'(t)||
    keel::Array<Expr> N; // principal unit normal vector N(t) = B(t) x T(t)
    keel::Array<Expr> B; // unit binormal vector B(t) = (r'(t) x r''(t)) / ||r'(t) x r''(t)||
    Expr speed;          // ds/dt = ||r'(t)||
    Expr curvature;      // kappa(t) = ||r'(t) x r''(t)|| / ||r'(t)||^3
    Expr torsion;        // tau(t) = ((r'(t) x r''(t)) . r'''(t)) / ||r'(t) x r''(t)||^2
    bool certified = false;
    keel::String reason;
};

// Compute the Frenet-Serret apparatus (T, N, B, speed, curvature kappa,
// torsion tau) of a parametric 3D (or 2D) curve r(t), certifying frame
// orthonormality and the Frenet-Serret derivative identities.
FrenetSerretResult frenetSerret(Ctx &c, keel::ArrayRef<Expr> curve,
                                Expr t, Budget *budget = nullptr);

struct SurfaceCurvatureResult
{
    Expr E;                   // r_u . r_u
    Expr F;                   // r_u . r_v
    Expr G;                   // r_v . r_v
    SymMatrix firstForm;      // 2x2 matrix I = [[E, F], [F, G]]
    Expr areaElement;         // sqrt(E*G - F^2) = ||r_u x r_v||
    keel::Array<Expr> normal; // unit surface normal n = (r_u x r_v) / ||r_u x r_v||
    Expr L;                   // r_uu . n
    Expr M;                   // r_uv . n
    Expr N;                   // r_vv . n
    SymMatrix secondForm;     // 2x2 matrix II = [[L, M], [M, N]]
    SymMatrix shapeOperator;  // 2x2 Weingarten matrix S = I^(-1) * II
    Expr gaussianCurvature;   // K = det(S) = (L*N - M^2) / (E*G - F^2)
    Expr meanCurvature;       // H = 1/2 * tr(S) = (E*N - 2*F*M + G*L) / (2*(E*G - F^2))
    bool certified = false;
    keel::String reason;
};

// Compute the 1st and 2nd fundamental forms, unit normal, Weingarten shape
// operator, Gaussian curvature K, and mean curvature H of a parametric surface
// r(u, v) in R^3.
SurfaceCurvatureResult surfaceCurvature(Ctx &c,
                                        keel::ArrayRef<Expr> surface,
                                        Expr u, Expr v,
                                        Budget *budget = nullptr);

struct ChristoffelResult
{
    SymMatrix metric;                 // g_{ij}
    SymMatrix inverseMetric;          // g^{ij}
    keel::Array<SymMatrix> firstKind; // firstKind[k].at(i, j) = Gamma_{k, ij}
    keel::Array<SymMatrix> secondKind;// secondKind[k].at(i, j) = Gamma^k_{ij}
    bool certified = false;
    keel::String reason;
};

// Compute the inverse metric g^{ij} and Christoffel symbols of the 1st and 2nd
// kind for a Riemannian or pseudo-Riemannian metric tensor g_{ij}(coords),
// certifying torsion-freeness (Gamma^k_{ij} == Gamma^k_{ji}) and metric
// compatibility (covariant derivative nabla_k g_{ij} == 0).
ChristoffelResult christoffelSymbols(Ctx &c, const SymMatrix &metric,
                                     keel::ArrayRef<Expr> coords,
                                     Budget *budget = nullptr);

struct RiemannCurvatureResult
{
    ChristoffelResult christoffel;
    // riemann[rho][sigma].at(mu, nu) = R^rho_{sigma, mu, nu}
    keel::Array<keel::Array<SymMatrix>> riemann;
    SymMatrix ricci;      // R_{sigma, nu} = sum_rho R^rho_{sigma, rho, nu}
    Expr scalarCurvature; // R = sum_{sigma, nu} g^{sigma, nu} R_{sigma, nu}
    SymMatrix einstein;   // G_{mu, nu} = R_{mu, nu} - 1/2 * R * g_{mu, nu}
    bool certified = false;
    keel::String reason;
};

// Compute the full Riemann curvature tensor R^rho_{sigma, mu, nu}, Ricci tensor
// R_{mu, nu}, scalar curvature R, and Einstein tensor G_{mu, nu}, certifying
// skew-symmetry and the first algebraic Bianchi identity.
RiemannCurvatureResult riemannTensor(Ctx &c, const SymMatrix &metric,
                                     keel::ArrayRef<Expr> coords,
                                     Budget *budget = nullptr);

SymMatrix ricciTensor(Ctx &c, const SymMatrix &metric,
                      keel::ArrayRef<Expr> coords,
                      Budget *budget = nullptr);

Expr scalarCurvature(Ctx &c, const SymMatrix &metric,
                     keel::ArrayRef<Expr> coords,
                     Budget *budget = nullptr);

struct GeodesicResult
{
    keel::Array<Expr> equations; // d2x^k/ds^2 + Gamma^k_{ij} * dx^i/ds * dx^j/ds
    keel::Array<Expr> rhs;       // explicit acceleration rhs: -Gamma^k_{ij} * dx^i/ds * dx^j/ds
    bool certified = false;
    keel::String reason;
};

// Construct the geodesic differential equations
//   d2x^k/ds^2 + sum_{i,j} Gamma^k_{ij} * (dx^i/ds) * (dx^j/ds) = 0
// for metric g_{ij}(coords), certifying equivalence with the Euler-Lagrange
// equations of the kinetic arc-length Lagrangian L = 1/2 * g_{ij} * dx^i * dx^j.
GeodesicResult geodesicEquations(Ctx &c, const SymMatrix &metric,
                                 keel::ArrayRef<Expr> coords,
                                 keel::ArrayRef<Expr> velocities = {},
                                 keel::ArrayRef<Expr> accelerations = {},
                                 Budget *budget = nullptr);

} // namespace numkit::cas
