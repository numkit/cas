// linalg/symmatrix.hpp — symbolic matrices, multivariable calculus, and exact linear algebra.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/core/expr.hpp>

#include <cstddef>
#include <string>
#include <vector>

namespace numkit::cas {

// Dense symbolic matrix over hash-consed `Expr` nodes.
class SymMatrix
{
public:
    SymMatrix() = default;
    SymMatrix(std::size_t rows, std::size_t cols, Expr fill = Expr{});
    SymMatrix(std::size_t rows, std::size_t cols, std::vector<Expr> entries);

    static SymMatrix zeros(Ctx &c, std::size_t rows, std::size_t cols);
    static SymMatrix eye(Ctx &c, std::size_t n);
    static SymMatrix diag(Ctx &c, const std::vector<Expr> &d);
    static SymMatrix column(const std::vector<Expr> &v);
    static SymMatrix row(const std::vector<Expr> &v);

    std::size_t rows() const { return rows_; }
    std::size_t cols() const { return cols_; }
    bool empty() const { return rows_ == 0 || cols_ == 0; }
    bool isSquare() const { return rows_ == cols_; }

    Expr &at(std::size_t r, std::size_t c)
    {
        return data_[r * cols_ + c];
    }
    const Expr &at(std::size_t r, std::size_t c) const
    {
        return data_[r * cols_ + c];
    }
    Expr &operator()(std::size_t r, std::size_t c) { return at(r, c); }
    const Expr &operator()(std::size_t r, std::size_t c) const { return at(r, c); }

    const std::vector<Expr> &data() const { return data_; }

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
    std::string toString(const Ctx &c) const;

private:
    std::size_t rows_ = 0;
    std::size_t cols_ = 0;
    std::vector<Expr> data_;
};

// Normalize a rational symbolic expression by combining sums of fractions
// over a common denominator, expanding polynomial numerators/denominators,
// and canceling univariate polynomial GCDs over Q[x] when applicable.
Expr simplifyRationalExpr(Ctx &c, Expr e);

// Multivariable vector calculus (MATLAB Symbolic Math Toolbox conventions):
//   - jacobian(c, funcs, vars): m x n matrix J(i, j) = df_i / dx_j
//   - gradient(c, f, vars):     n x 1 column vector grad(i, 0) = df / dx_i
//   - hessian(c, f, vars):      n x n symmetric matrix H(i, j) = d^2f / (dx_i dx_j)
SymMatrix jacobian(Ctx &c, const std::vector<Expr> &funcs,
                   const std::vector<Expr> &vars);
SymMatrix gradient(Ctx &c, Expr f, const std::vector<Expr> &vars);
SymMatrix hessian(Ctx &c, Expr f, const std::vector<Expr> &vars);

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
std::vector<SymMatrix> nullspace(Ctx &c, const SymMatrix &A,
                                 Budget *budget = nullptr);

struct EigenPair
{
    Expr lambda;                    // eigenvalue
    std::size_t multiplicity = 1;   // algebraic multiplicity in charpoly(A)
    std::vector<SymMatrix> vectors; // geometric eigenspace basis: n x 1 columns v with (A - lambda*I)*v = 0
};

// Compute the symbolic/real eigenvalues of a square matrix A (roots of
// charpoly(A, lambda) = 0), repeated according to their algebraic multiplicity.
std::vector<Expr> eigenvalues(Ctx &c, const SymMatrix &A,
                              Budget *budget = nullptr);

// Compute the eigenpairs (lambda, algebraic multiplicity, basis of ker(A - lambda*I))
// of a square matrix A.
std::vector<EigenPair> eigenvectors(Ctx &c, const SymMatrix &A,
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
               std::vector<std::size_t> *pivotColsOut = nullptr,
               Budget *budget = nullptr);

// Compute the exact rank of an m x n symbolic matrix A (number of pivot
// columns in its RREF; 0 for an empty matrix).
std::size_t rank(Ctx &c, const SymMatrix &A, Budget *budget = nullptr);

struct LUDecomposition
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    SymMatrix L;                    // m x m unit lower-triangular matrix (L(i, i) == 1)
    SymMatrix U;                    // m x n upper-triangular (row-echelon) matrix
    SymMatrix P;                    // m x m row-permutation matrix: P * A == L * U
    std::vector<std::size_t> perm;  // row permutation indices (P(i, perm[i]) == 1)
    int sign = 1;                   // determinant sign of P (+1 or -1)
    std::string reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Compute the exact pivoted LU decomposition P * A = L * U of an m x n
// symbolic matrix A, certified by verifying P * A == L * U, unit lower-
// triangularity of L, and upper-triangularity of U.
LUDecomposition lu(Ctx &c, const SymMatrix &A, Budget *budget = nullptr);

// Perform exact Gram-Schmidt orthogonalization (or orthonormalization when
// `normalize == true`) on a sequence of m x 1 column vectors, dropping any
// vector that lies in the span of previous vectors.
std::vector<SymMatrix> gramSchmidt(Ctx &c,
                                   const std::vector<SymMatrix> &cols,
                                   bool normalize = true,
                                   Budget *budget = nullptr);

struct QRDecomposition
{
    enum class Status { Unevaluated, ProvedSymbolic };

    Status status = Status::Unevaluated;
    SymMatrix Q; // m x n column-orthonormal matrix (Q^T * Q == I_n)
    SymMatrix R; // n x n upper-triangular matrix: A == Q * R
    std::string reason;

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
    std::string reason;

    bool proved() const { return status == Status::ProvedSymbolic; }
};

// Compute the exact Jordan canonical form A = P * J * P^(-1) of a square
// matrix A whose eigenvalues lie in the solvable symbolic/radical domain,
// certified by verifying A * P == P * J and P * PInv == I_n.
JordanDecomposition jordanForm(Ctx &c, const SymMatrix &A,
                               Budget *budget = nullptr);

} // namespace numkit::cas
