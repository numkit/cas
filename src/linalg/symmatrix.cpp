#include <numkit/cas/linalg/symmatrix.hpp>

#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/poly/upoly.hpp>

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <vector>

namespace numkit::cas {

namespace {

bool checkLinalgBudget(const Ctx &c, Budget *budget)
{
    if (!budget)
        return true;
    return budget->step() && budget->recordArenaBytes(c.nodeCount() * 32);
}

void collectSymbolsAndCheckPureRat(const Ctx &c, Expr e,
                                   std::vector<Expr> &syms, bool &pureRat)
{
    if (e.isNull()) {
        pureRat = false;
        return;
    }
    switch (c.kind(e)) {
    case NodeKind::Number:
        return;
    case NodeKind::Symbol:
        if (std::find(syms.begin(), syms.end(), e) == syms.end())
            syms.push_back(e);
        return;
    case NodeKind::RootOf:
    case NodeKind::Func:
        pureRat = false;
        return;
    case NodeKind::Pow: {
        collectSymbolsAndCheckPureRat(c, c.child(e, 0), syms, pureRat);
        const Expr ex = c.child(e, 1);
        if (c.kind(ex) != NodeKind::Number ||
            !(c.numberValue(ex).den() == BigInt(1))) {
            pureRat = false;
        }
        return;
    }
    case NodeKind::Add:
    case NodeKind::Mul:
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            collectSymbolsAndCheckPureRat(c, c.child(e, i), syms, pureRat);
        return;
    }
}

Expr upolyToExpr(Ctx &c, const UPoly &p, Expr var)
{
    if (p.isZero())
        return c.zero();
    std::vector<Expr> terms;
    for (std::size_t i = 0; i < p.coeffs().size(); ++i) {
        const Rational &k = p.coeff(i);
        if (k.isZero())
            continue;
        if (i == 0) {
            terms.push_back(c.number(k));
        } else if (i == 1) {
            terms.push_back(c.mul({c.number(k), var}));
        } else {
            terms.push_back(c.mul(
                {c.number(k), c.pow(var, c.number(static_cast<std::int64_t>(i)))}));
        }
    }
    return terms.empty() ? c.zero() : c.add(terms);
}

struct FormalFrac
{
    Expr num;
    Expr den;
};

FormalFrac toFormalFrac(Ctx &c, Expr e)
{
    if (e.isNull())
        return {Expr(), Expr()};
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return {e, c.one()};
    case NodeKind::Func: {
        const Expr arg = simplifyRationalExpr(c, c.child(e, 0));
        if (arg.isNull())
            return {Expr(), Expr()};
        const Expr fn = c.func(c.funcName(e), arg);
        Rational r;
        if (c.evalExact(fn, {}, r))
            return {c.number(r), c.one()};
        return {fn, c.one()};
    }
    case NodeKind::Pow: {
        const Expr b = c.child(e, 0);
        const Expr ex = c.child(e, 1);
        if (c.kind(ex) == NodeKind::Number) {
            const Rational &rv = c.numberValue(ex);
            std::int64_t k = 0;
            if (rv.den() == BigInt(1) && rv.num().fitsInt64(k) &&
                std::abs(k) <= 64) {
                const FormalFrac bf = toFormalFrac(c, b);
                if (bf.num.isNull() || bf.den.isNull())
                    return {Expr(), Expr()};
                if (k == 0)
                    return {c.one(), c.one()};
                if (k > 0) {
                    const Expr ek = c.number(k);
                    return {c.expand(c.pow(bf.num, ek)),
                            c.expand(c.pow(bf.den, ek))};
                }
                if (c.isZero(bf.num))
                    return {Expr(), Expr()};
                const Expr ek = c.number(-k);
                return {c.expand(c.pow(bf.den, ek)),
                        c.expand(c.pow(bf.num, ek))};
            }
        }
        const Expr sb = simplifyRationalExpr(c, b);
        const Expr sex = simplifyRationalExpr(c, ex);
        if (sb.isNull() || sex.isNull())
            return {Expr(), Expr()};
        return {c.expand(c.pow(sb, sex)), c.one()};
    }
    case NodeKind::Mul: {
        Expr numAcc = c.one();
        Expr denAcc = c.one();
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const FormalFrac cf = toFormalFrac(c, c.child(e, i));
            if (cf.num.isNull() || cf.den.isNull())
                return {Expr(), Expr()};
            numAcc = c.expand(c.mul({numAcc, cf.num}));
            denAcc = c.expand(c.mul({denAcc, cf.den}));
        }
        return {numAcc, denAcc};
    }
    case NodeKind::Add: {
        Expr numAcc = c.zero();
        Expr denAcc = c.one();
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const FormalFrac cf = toFormalFrac(c, c.child(e, i));
            if (cf.num.isNull() || cf.den.isNull())
                return {Expr(), Expr()};
            if (c.isZero(cf.num))
                continue;
            if (c.isZero(numAcc)) {
                numAcc = cf.num;
                denAcc = cf.den;
            } else if (denAcc == cf.den) {
                numAcc = c.expand(c.add({numAcc, cf.num}));
            } else {
                numAcc = c.expand(
                    c.add({c.mul({numAcc, cf.den}), c.mul({cf.num, denAcc})}));
                denAcc = c.expand(c.mul({denAcc, cf.den}));
            }
            if (c.isZero(numAcc))
                denAcc = c.one();
        }
        return {numAcc, denAcc};
    }
    }
    return {e, c.one()};
}

bool isZeroSymbolic(Ctx &c, Expr e)
{
    if (e.isNull())
        return false;
    if (c.isZero(e))
        return true;
    const Expr s = simplifyRationalExpr(c, e);
    return !s.isNull() && c.isZero(s);
}

} // namespace

Expr simplifyRationalExpr(Ctx &c, Expr e)
{
    if (e.isNull())
        return Expr();
    Rational r;
    if (c.evalExact(e, {}, r))
        return c.number(r);

    const FormalFrac f = toFormalFrac(c, e);
    if (f.num.isNull() || f.den.isNull() || c.isZero(f.den))
        return Expr();
    if (c.isZero(f.num))
        return c.zero();
    if (f.den == c.one())
        return f.num;
    if (f.num == f.den)
        return c.one();
    if (c.isZero(c.expand(c.add({f.num, f.den}))))
        return c.number(std::int64_t{-1});
    if (c.kind(f.den) == NodeKind::Number) {
        return c.expand(
            c.mul({c.number(Rational(std::int64_t{1}) / c.numberValue(f.den)),
                   f.num}));
    }

    // Univariate polynomial GCD cancellation in Q(var).
    std::vector<Expr> syms;
    bool pureRat = true;
    collectSymbolsAndCheckPureRat(c, f.num, syms, pureRat);
    collectSymbolsAndCheckPureRat(c, f.den, syms, pureRat);
    if (pureRat && syms.size() == 1) {
        UPoly upN, upD;
        const Expr combined = c.div(f.num, f.den);
        if (!combined.isNull() && toRational(c, combined, syms[0], upN, upD)) {
            const Expr rN = upolyToExpr(c, upN, syms[0]);
            if (upD.isConst()) {
                // toRational makes upD monic, so constant upD == 1.
                return c.expand(
                    c.mul({c.number(Rational(std::int64_t{1}) / upD.coeff(0)),
                           rN}));
            }
            const Expr rD = upolyToExpr(c, upD, syms[0]);
            return c.div(rN, rD);
        }
    }

    return c.div(f.num, f.den);
}

// ============================================================================
// SymMatrix methods
// ============================================================================

SymMatrix::SymMatrix(std::size_t rows, std::size_t cols, Expr fill)
    : rows_(rows), cols_(cols), data_(rows * cols, fill)
{
}

SymMatrix::SymMatrix(std::size_t rows, std::size_t cols,
                     std::vector<Expr> entries)
    : rows_(rows), cols_(cols), data_(std::move(entries))
{
    assert(data_.size() == rows_ * cols_);
}

SymMatrix SymMatrix::zeros(Ctx &c, std::size_t rows, std::size_t cols)
{
    return SymMatrix(rows, cols, c.zero());
}

SymMatrix SymMatrix::eye(Ctx &c, std::size_t n)
{
    SymMatrix m = zeros(c, n, n);
    const Expr one = c.one();
    for (std::size_t i = 0; i < n; ++i)
        m.at(i, i) = one;
    return m;
}

SymMatrix SymMatrix::diag(Ctx &c, const std::vector<Expr> &d)
{
    const std::size_t n = d.size();
    SymMatrix m = zeros(c, n, n);
    for (std::size_t i = 0; i < n; ++i)
        m.at(i, i) = d[i];
    return m;
}

SymMatrix SymMatrix::column(const std::vector<Expr> &v)
{
    return SymMatrix(v.size(), 1, v);
}

SymMatrix SymMatrix::row(const std::vector<Expr> &v)
{
    return SymMatrix(1, v.size(), v);
}

SymMatrix SymMatrix::transpose() const
{
    SymMatrix out(cols_, rows_);
    for (std::size_t r = 0; r < rows_; ++r)
        for (std::size_t col = 0; col < cols_; ++col)
            out.at(col, r) = at(r, col);
    return out;
}

SymMatrix SymMatrix::add(Ctx &c, const SymMatrix &other) const
{
    if (rows_ != other.rows_ || cols_ != other.cols_)
        return SymMatrix();
    SymMatrix out(rows_, cols_);
    for (std::size_t i = 0; i < data_.size(); ++i)
        out.data_[i] = simplifyRationalExpr(c, c.add({data_[i], other.data_[i]}));
    return out;
}

SymMatrix SymMatrix::sub(Ctx &c, const SymMatrix &other) const
{
    if (rows_ != other.rows_ || cols_ != other.cols_)
        return SymMatrix();
    SymMatrix out(rows_, cols_);
    for (std::size_t i = 0; i < data_.size(); ++i)
        out.data_[i] =
            simplifyRationalExpr(c, c.add({data_[i], c.neg(other.data_[i])}));
    return out;
}

SymMatrix SymMatrix::mul(Ctx &c, const SymMatrix &other) const
{
    if (cols_ != other.rows_)
        return SymMatrix();
    SymMatrix out(rows_, other.cols_, c.zero());
    for (std::size_t i = 0; i < rows_; ++i) {
        for (std::size_t j = 0; j < other.cols_; ++j) {
            std::vector<Expr> terms;
            for (std::size_t k = 0; k < cols_; ++k) {
                const Expr a = at(i, k);
                const Expr b = other.at(k, j);
                if (!c.isZero(a) && !c.isZero(b))
                    terms.push_back(c.mul({a, b}));
            }
            out.at(i, j) = terms.empty()
                               ? c.zero()
                               : simplifyRationalExpr(c, c.add(terms));
        }
    }
    return out;
}

SymMatrix SymMatrix::scale(Ctx &c, Expr scalar) const
{
    SymMatrix out(rows_, cols_);
    for (std::size_t i = 0; i < data_.size(); ++i)
        out.data_[i] = simplifyRationalExpr(c, c.mul({scalar, data_[i]}));
    return out;
}

SymMatrix SymMatrix::expand(Ctx &c) const
{
    SymMatrix out(rows_, cols_);
    for (std::size_t i = 0; i < data_.size(); ++i)
        out.data_[i] = simplifyRationalExpr(c, data_[i]);
    return out;
}

SymMatrix SymMatrix::diff(Ctx &c, Expr var) const
{
    SymMatrix out(rows_, cols_);
    for (std::size_t i = 0; i < data_.size(); ++i)
        out.data_[i] = simplifyRationalExpr(c, c.diff(data_[i], var));
    return out;
}

SymMatrix SymMatrix::subs(Ctx &c, Expr from, Expr to) const
{
    SymMatrix out(rows_, cols_);
    for (std::size_t i = 0; i < data_.size(); ++i)
        out.data_[i] = simplifyRationalExpr(c, c.subs(data_[i], from, to));
    return out;
}

Expr SymMatrix::trace(Ctx &c) const
{
    if (!isSquare())
        return Expr();
    if (rows_ == 0)
        return c.zero();
    std::vector<Expr> diagTerms;
    diagTerms.reserve(rows_);
    for (std::size_t i = 0; i < rows_; ++i)
        diagTerms.push_back(at(i, i));
    return simplifyRationalExpr(c, c.add(diagTerms));
}

std::string SymMatrix::toString(const Ctx &c) const
{
    std::string out = "[";
    for (std::size_t r = 0; r < rows_; ++r) {
        if (r > 0)
            out += "; ";
        for (std::size_t col = 0; col < cols_; ++col) {
            if (col > 0)
                out += ", ";
            out += c.toString(at(r, col));
        }
    }
    out += "]";
    return out;
}

// ============================================================================
// Multivariable Calculus: jacobian, gradient, hessian
// ============================================================================

SymMatrix jacobian(Ctx &c, const std::vector<Expr> &funcs,
                   const std::vector<Expr> &vars)
{
    SymMatrix J(funcs.size(), vars.size());
    for (std::size_t i = 0; i < funcs.size(); ++i) {
        for (std::size_t j = 0; j < vars.size(); ++j) {
            J.at(i, j) = simplifyRationalExpr(c, c.diff(funcs[i], vars[j]));
        }
    }
    return J;
}

SymMatrix gradient(Ctx &c, Expr f, const std::vector<Expr> &vars)
{
    SymMatrix g(vars.size(), 1);
    for (std::size_t i = 0; i < vars.size(); ++i)
        g.at(i, 0) = simplifyRationalExpr(c, c.diff(f, vars[i]));
    return g;
}

SymMatrix hessian(Ctx &c, Expr f, const std::vector<Expr> &vars)
{
    const std::size_t n = vars.size();
    SymMatrix H(n, n);
    std::vector<Expr> df(n);
    for (std::size_t i = 0; i < n; ++i)
        df[i] = c.diff(f, vars[i]);

    for (std::size_t i = 0; i < n; ++i) {
        for (std::size_t j = i; j < n; ++j) {
            const Expr d2 = simplifyRationalExpr(c, c.diff(df[i], vars[j]));
            H.at(i, j) = d2;
            H.at(j, i) = d2;
        }
    }
    return H;
}

// ============================================================================
// Faddeev-LeVerrier: charpoly, adjugate, det, inv
// ============================================================================

namespace {

// Faddeev-LeVerrier recurrence for an n x n matrix A:
//   p(lambda) = det(lambda * I - A) = sum_{j=0}^n coeffs[j] * lambda^j,
//   where coeffs[n] = 1, coeffs[0] = (-1)^n * det(A),
//   and adj(A) = (-1)^(n-1) * B_n satisfies A * adj(A) = det(A) * I.
bool faddeevLeVerrier(Ctx &c, const SymMatrix &A, Budget *budget,
                      std::vector<Expr> &coeffs, SymMatrix &adjOut)
{
    if (!A.isSquare())
        return false;
    const std::size_t n = A.rows();
    coeffs.assign(n + 1, c.zero());
    coeffs[n] = c.one();
    if (n == 0) {
        adjOut = SymMatrix(0, 0);
        return true;
    }

    const SymMatrix I = SymMatrix::eye(c, n);
    SymMatrix B = SymMatrix::zeros(c, n, n);
    for (std::size_t k = 1; k <= n; ++k) {
        if (!checkLinalgBudget(c, budget))
            return false;
        if (k == 1) {
            B = I;
        } else {
            const SymMatrix AB = A.mul(c, B);
            B = AB.add(c, I.scale(c, coeffs[n - k + 1]));
        }
        const SymMatrix AB = A.mul(c, B);
        const Expr tr = AB.trace(c);
        if (tr.isNull())
            return false;
        const Expr ck = simplifyRationalExpr(
            c, c.mul({c.number(Rational(std::int64_t{-1}, BigInt(k))), tr}));
        if (ck.isNull())
            return false;
        coeffs[n - k] = ck;
        if (k == n) {
            adjOut = ((n - 1) % 2 == 0) ? B : B.scale(c, c.number(std::int64_t{-1}));
        }
    }
    return true;
}

} // namespace

Expr charpoly(Ctx &c, const SymMatrix &A, Expr lambda, Budget *budget)
{
    if (!A.isSquare() || lambda.isNull())
        return Expr();
    std::vector<Expr> coeffs;
    SymMatrix adj;
    if (!faddeevLeVerrier(c, A, budget, coeffs, adj))
        return Expr();

    std::vector<Expr> terms;
    for (std::size_t j = 0; j < coeffs.size(); ++j) {
        if (c.isZero(coeffs[j]))
            continue;
        if (j == 0) {
            terms.push_back(coeffs[j]);
        } else if (j == 1) {
            terms.push_back(c.mul({coeffs[j], lambda}));
        } else {
            terms.push_back(c.mul(
                {coeffs[j], c.pow(lambda, c.number(static_cast<std::int64_t>(j)))}));
        }
    }
    return terms.empty() ? c.zero() : simplifyRationalExpr(c, c.add(terms));
}

SymMatrix adjugate(Ctx &c, const SymMatrix &A, Budget *budget)
{
    std::vector<Expr> coeffs;
    SymMatrix adj;
    if (!faddeevLeVerrier(c, A, budget, coeffs, adj))
        return SymMatrix();
    return adj;
}

Expr det(Ctx &c, const SymMatrix &A, Budget *budget)
{
    if (!A.isSquare())
        return Expr();
    const std::size_t n = A.rows();
    if (n == 0)
        return c.one();
    if (n == 1)
        return simplifyRationalExpr(c, A.at(0, 0));
    if (n == 2) {
        return simplifyRationalExpr(
            c, c.add({c.mul({A.at(0, 0), A.at(1, 1)}),
                      c.neg(c.mul({A.at(0, 1), A.at(1, 0)}))}));
    }
    std::vector<Expr> coeffs;
    SymMatrix adj;
    if (!faddeevLeVerrier(c, A, budget, coeffs, adj))
        return Expr();
    // coeffs[0] = (-1)^n * det(A)
    return (n % 2 == 0)
               ? coeffs[0]
               : simplifyRationalExpr(c, c.neg(coeffs[0]));
}

SymMatrix inv(Ctx &c, const SymMatrix &A, Budget *budget)
{
    if (!A.isSquare() || A.empty())
        return SymMatrix();
    const std::size_t n = A.rows();
    std::vector<Expr> coeffs;
    SymMatrix adj;
    if (!faddeevLeVerrier(c, A, budget, coeffs, adj))
        return SymMatrix();

    const Expr detA =
        (n % 2 == 0) ? coeffs[0] : simplifyRationalExpr(c, c.neg(coeffs[0]));
    if (detA.isNull() || isZeroSymbolic(c, detA))
        return SymMatrix(); // singular matrix

    const Expr invDet = c.pow(detA, c.number(std::int64_t{-1}));
    return adj.scale(c, invDet);
}

// ============================================================================
// Exact Symbolic Linear System Solver: linsolve(A, B)
// ============================================================================

SymMatrix linsolve(Ctx &c, const SymMatrix &A, const SymMatrix &B,
                   Budget *budget)
{
    if (A.empty() || B.empty() || A.rows() != B.rows())
        return SymMatrix();
    const std::size_t m = A.rows();
    const std::size_t n = A.cols();
    const std::size_t rhsCols = B.cols();
    if (m < n)
        return SymMatrix(); // underdetermined

    // Fast division-free path for square systems (m == n):
    // Compute adj(A) and det(A) via Faddeev-LeVerrier, multiply Y = adj(A) * B
    // in the polynomial ring first, and divide by det(A) once at the end.
    if (m == n) {
        std::vector<Expr> coeffs;
        SymMatrix adj;
        if (faddeevLeVerrier(c, A, budget, coeffs, adj)) {
            const Expr detA =
                (n % 2 == 0) ? coeffs[0]
                             : simplifyRationalExpr(c, c.neg(coeffs[0]));
            if (detA.isNull() || isZeroSymbolic(c, detA))
                return SymMatrix(); // singular matrix
            const SymMatrix Y = adj.mul(c, B);
            const Expr invDet = c.pow(detA, c.number(std::int64_t{-1}));
            return Y.scale(c, invDet);
        }
        if (budget && !budget->ok())
            return SymMatrix();
    }

    // Copy A and B into working matrices with rational-normalized entries.
    SymMatrix M = A.expand(c);
    SymMatrix R = B.expand(c);

    // Forward Gaussian elimination with partial pivot selection (preferring
    // constant / low-cost non-zero pivots to keep intermediate expressions small).
    for (std::size_t col = 0; col < n; ++col) {
        if (!checkLinalgBudget(c, budget))
            return SymMatrix();

        std::size_t pivotRow = m;
        std::size_t bestCost = static_cast<std::size_t>(-1);
        for (std::size_t r = col; r < m; ++r) {
            const Expr cand = M.at(r, col);
            if (!isZeroSymbolic(c, cand)) {
                const std::size_t cost = c.exprCost(cand);
                if (cost < bestCost) {
                    bestCost = cost;
                    pivotRow = r;
                }
            }
        }
        if (pivotRow == m)
            return SymMatrix(); // rank < n (singular / underdetermined)

        if (pivotRow != col) {
            for (std::size_t j = col; j < n; ++j)
                std::swap(M.at(col, j), M.at(pivotRow, j));
            for (std::size_t j = 0; j < rhsCols; ++j)
                std::swap(R.at(col, j), R.at(pivotRow, j));
        }

        const Expr pivot = M.at(col, col);
        const Expr invPivot = c.pow(pivot, c.number(std::int64_t{-1}));

        for (std::size_t r = col + 1; r < m; ++r) {
            if (!checkLinalgBudget(c, budget))
                return SymMatrix();
            const Expr entry = M.at(r, col);
            if (isZeroSymbolic(c, entry)) {
                M.at(r, col) = c.zero();
                continue;
            }
            const Expr factor =
                simplifyRationalExpr(c, c.mul({entry, invPivot}));
            M.at(r, col) = c.zero();
            for (std::size_t j = col + 1; j < n; ++j) {
                M.at(r, j) = simplifyRationalExpr(
                    c, c.add({M.at(r, j), c.neg(c.mul({factor, M.at(col, j)}))}));
            }
            for (std::size_t j = 0; j < rhsCols; ++j) {
                R.at(r, j) = simplifyRationalExpr(
                    c, c.add({R.at(r, j), c.neg(c.mul({factor, R.at(col, j)}))}));
            }
        }
    }

    // For overdetermined systems (m > n), verify consistency of residual rows.
    for (std::size_t r = n; r < m; ++r) {
        for (std::size_t j = 0; j < rhsCols; ++j) {
            if (!isZeroSymbolic(c, R.at(r, j)))
                return SymMatrix(); // inconsistent system
        }
    }

    // Back-substitution for the n x rhsCols solution X.
    SymMatrix X(n, rhsCols, c.zero());
    for (std::size_t idx = n; idx > 0; --idx) {
        if (!checkLinalgBudget(c, budget))
            return SymMatrix();
        const std::size_t i = idx - 1;
        const Expr invDiag = c.pow(M.at(i, i), c.number(std::int64_t{-1}));
        for (std::size_t j = 0; j < rhsCols; ++j) {
            std::vector<Expr> sumTerms;
            sumTerms.push_back(R.at(i, j));
            for (std::size_t k = i + 1; k < n; ++k) {
                if (!c.isZero(M.at(i, k)) && !c.isZero(X.at(k, j))) {
                    sumTerms.push_back(c.neg(c.mul({M.at(i, k), X.at(k, j)})));
                }
            }
            const Expr rhsVal = simplifyRationalExpr(c, c.add(sumTerms));
            X.at(i, j) = simplifyRationalExpr(c, c.mul({rhsVal, invDiag}));
        }
    }

    return X;
}

} // namespace numkit::cas
