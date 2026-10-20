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

} // namespace numkit::cas
