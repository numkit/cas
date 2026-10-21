#include <numkit/cas/linalg/symmatrix.hpp>

#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/core/symsolve.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/poly/upoly.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>
#include <numkit/cas/transform/laplace.hpp>

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
            if (rv.signum() < 0) {
                const Expr sb = simplifyRationalExpr(c, b);
                if (sb.isNull() || c.isZero(sb))
                    return {Expr(), Expr()};
                return {c.one(), c.expand(c.pow(sb, c.number(-rv)))};
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

// Extract the common monomial factor and leading rational coefficient from an
// expanded sum `e`, writing `e = scaleMonomOut * primOut` where `primOut` has
// no common factor across its additive terms and unit leading rational coeff.
void splitMonomialAndScale(Ctx &c, Expr e, Expr &scaleMonomOut, Expr &primOut)
{
    std::vector<Expr> terms;
    if (c.kind(e) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            terms.push_back(c.child(e, i));
    } else {
        terms.push_back(e);
    }

    auto decomposeTerm = [&](Expr t,
                             std::vector<std::pair<Expr, std::int64_t>> &facs) {
        auto inspect = [&](Expr f) {
            if (c.kind(f) == NodeKind::Number)
                return;
            if (c.kind(f) == NodeKind::Pow &&
                c.kind(c.child(f, 1)) == NodeKind::Number) {
                const Rational &rv = c.numberValue(c.child(f, 1));
                std::int64_t k = 0;
                if (rv.den() == BigInt(1) && rv.num().fitsInt64(k) && k >= 1) {
                    facs.emplace_back(c.child(f, 0), k);
                    return;
                }
            }
            facs.emplace_back(f, 1);
        };
        if (c.kind(t) == NodeKind::Mul) {
            for (std::size_t i = 0; i < c.childCount(t); ++i)
                inspect(c.child(t, i));
        } else {
            inspect(t);
        }
    };

    std::vector<std::pair<Expr, std::int64_t>> common;
    decomposeTerm(terms[0], common);
    for (std::size_t i = 1; i < terms.size() && !common.empty(); ++i) {
        std::vector<std::pair<Expr, std::int64_t>> cur;
        decomposeTerm(terms[i], cur);
        std::vector<std::pair<Expr, std::int64_t>> nextCommon;
        for (const auto & cf : common) {
            for (const auto &tf : cur) {
                if (cf.first == tf.first) {
                    nextCommon.emplace_back(cf.first,
                                            std::min(cf.second, tf.second));
                    break;
                }
            }
        }
        common = std::move(nextCommon);
    }

    std::vector<Expr> monomFacs;
    std::vector<Expr> invMonomFacs;
    for (const auto &cf : common) {
        monomFacs.push_back(c.pow(cf.first, c.number(cf.second)));
        invMonomFacs.push_back(c.pow(cf.first, c.number(-cf.second)));
    }
    const Expr monom = monomFacs.empty() ? c.one() : c.mul(monomFacs);
    const Expr invMonom = invMonomFacs.empty() ? c.one() : c.mul(invMonomFacs);

    const Expr rawPrim =
        invMonomFacs.empty() ? e : c.expand(c.mul({e, invMonom}));

    // Normalize by the rational coefficient of the first additive term of rawPrim.
    const Expr firstTerm =
        (c.kind(rawPrim) == NodeKind::Add && c.childCount(rawPrim) > 0)
            ? c.child(rawPrim, 0)
            : rawPrim;
    Rational leadCoef(std::int64_t{1});
    if (c.kind(firstTerm) == NodeKind::Number) {
        leadCoef = c.numberValue(firstTerm);
    } else if (c.kind(firstTerm) == NodeKind::Mul &&
               c.childCount(firstTerm) > 0 &&
               c.kind(c.child(firstTerm, 0)) == NodeKind::Number) {
        leadCoef = c.numberValue(c.child(firstTerm, 0));
    }
    if (leadCoef.isZero())
        leadCoef = Rational(std::int64_t{1});

    scaleMonomOut = c.mul({c.number(leadCoef), monom});
    primOut = (leadCoef == Rational(std::int64_t{1}))
                  ? rawPrim
                  : c.expand(c.mul(
                        {c.number(Rational(std::int64_t{1}) / leadCoef),
                         rawPrim}));
}

} // namespace

Expr simplifyRationalExpr(Ctx &c, Expr e)
{
    if (e.isNull())
        return Expr();
    Rational r;
    if (c.evalExact(e, {}, r))
        return c.number(r);

    FormalFrac f = toFormalFrac(c, e);
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

    // Cancel common monomial content and proportional cofactor sums.
    {
        Expr smNum, primNum, smDen, primDen;
        splitMonomialAndScale(c, f.num, smNum, primNum);
        splitMonomialAndScale(c, f.den, smDen, primDen);
        const Expr smRatio = c.div(smNum, smDen);
        if (primNum == primDen) {
            return smRatio;
        }
        Expr newNum, newDen;
        FormalFrac smFrac = toFormalFrac(c, smRatio);
        if (!smFrac.num.isNull() && !smFrac.den.isNull()) {
            f.num = c.expand(c.mul({smFrac.num, primNum}));
            f.den = c.expand(c.mul({smFrac.den, primDen}));
            if (f.den == c.one())
                return f.num;
        }
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

namespace {

bool isZeroLinalg(Ctx &c, Expr e, Budget *budget)
{
    if (e.isNull())
        return false;
    if (c.isZero(e))
        return true;
    const Expr expd = c.expand(e);
    if (!expd.isNull() && c.isZero(expd))
        return true;
    const Expr r = simplifyRationalExpr(c, expd.isNull() ? e : expd);
    if (!r.isNull() && c.isZero(r))
        return true;
    const Expr s = simplify(c, r.isNull() ? e : r, budget);
    if (!s.isNull() && c.isZero(s))
        return true;
    const Expr sr = simplifyRationalExpr(c, s);
    return !sr.isNull() && c.isZero(sr);
}

Expr normLinalg(Ctx &c, Expr e, Budget *budget)
{
    if (e.isNull())
        return c.zero();
    if (c.isZero(e) || c.kind(e) == NodeKind::Number)
        return e;
    const Expr expd = c.expand(e);
    if (!expd.isNull() && c.isZero(expd))
        return c.zero();
    Expr r = simplifyRationalExpr(c, expd.isNull() ? e : expd);
    if (r.isNull())
        r = expd.isNull() ? e : expd;
    if (c.isZero(r) || c.kind(r) == NodeKind::Number)
        return r;
    const Expr s = simplify(c, r, budget);
    if (!s.isNull()) {
        if (c.isZero(s))
            return c.zero();
        const Expr sr = simplifyRationalExpr(c, s);
        if (!sr.isNull() && c.isZero(sr))
            return c.zero();
        return s;
    }
    return r;
}

// Compute Reduced Row Echelon Form (RREF) of an m x cols matrix M, pivoting on
// the first `pivotColLimit` columns. Populates `pivotCols` with the column index
// of each pivot row.
bool computeRREF(Ctx &c, SymMatrix &M, std::size_t pivotColLimit,
                 std::vector<std::size_t> &pivotCols, Budget *budget)
{
    const std::size_t m = M.rows();
    const std::size_t cols = M.cols();
    pivotCols.clear();

    for (std::size_t r = 0; r < m; ++r)
        for (std::size_t j = 0; j < cols; ++j)
            M.at(r, j) = normLinalg(c, M.at(r, j), budget);

    std::size_t curRow = 0;
    for (std::size_t col = 0; col < pivotColLimit && curRow < m; ++col) {
        if (!checkLinalgBudget(c, budget))
            return false;

        std::size_t pivotRow = m;
        std::size_t bestCost = static_cast<std::size_t>(-1);
        for (std::size_t r = curRow; r < m; ++r) {
            const Expr cand = M.at(r, col);
            if (!isZeroLinalg(c, cand, budget)) {
                const std::size_t cost = c.exprCost(cand);
                if (cost < bestCost) {
                    bestCost = cost;
                    pivotRow = r;
                }
            } else {
                M.at(r, col) = c.zero();
            }
        }
        if (pivotRow == m)
            continue;

        if (pivotRow != curRow) {
            for (std::size_t j = 0; j < cols; ++j)
                std::swap(M.at(curRow, j), M.at(pivotRow, j));
        }

        const Expr pivot = M.at(curRow, col);
        const Expr invPivot = c.pow(pivot, c.number(std::int64_t{-1}));

        // Eliminate column `col` in all other rows r != curRow using
        // cross-multiplied numerator (pivot * M(r, j) - M(r, col) * M(curRow, j))
        // first so conjugate radical products cancel to 0 before dividing by pivot.
        for (std::size_t r = 0; r < m; ++r) {
            if (r == curRow)
                continue;
            if (!checkLinalgBudget(c, budget))
                return false;
            const Expr entry = M.at(r, col);
            if (isZeroLinalg(c, entry, budget)) {
                M.at(r, col) = c.zero();
                continue;
            }
            M.at(r, col) = c.zero();
            for (std::size_t j = col + 1; j < cols; ++j) {
                const Expr crossNum = c.expand(
                    c.add({c.mul({pivot, M.at(r, j)}),
                           c.neg(c.mul({entry, M.at(curRow, j)}))}));
                if (isZeroLinalg(c, crossNum, budget)) {
                    M.at(r, j) = c.zero();
                } else {
                    M.at(r, j) =
                        normLinalg(c, c.mul({crossNum, invPivot}), budget);
                }
            }
        }

        // Normalize the pivot row so M(curRow, col) == 1.
        M.at(curRow, col) = c.one();
        for (std::size_t j = col + 1; j < cols; ++j) {
            if (!c.isZero(M.at(curRow, j))) {
                M.at(curRow, j) =
                    normLinalg(c, c.mul({M.at(curRow, j), invPivot}), budget);
            }
        }

        pivotCols.push_back(col);
        ++curRow;
    }
    return true;
}

// Find one particular solution x to a (possibly rank-deficient) linear system
// A * x = b using RREF on the augmented matrix [A | b], setting free variables to 0.
SymMatrix linsolveParticular(Ctx &c, const SymMatrix &A, const SymMatrix &b,
                             Budget *budget)
{
    if (A.empty() || b.empty() || A.rows() != b.rows() || b.cols() != 1)
        return SymMatrix();
    const std::size_t m = A.rows();
    const std::size_t n = A.cols();

    SymMatrix aug(m, n + 1, c.zero());
    for (std::size_t r = 0; r < m; ++r) {
        for (std::size_t j = 0; j < n; ++j)
            aug.at(r, j) = A.at(r, j);
        aug.at(r, n) = b.at(r, 0);
    }

    std::vector<std::size_t> pivotCols;
    if (!computeRREF(c, aug, n, pivotCols, budget))
        return SymMatrix();

    // Check consistency on non-pivot rows
    for (std::size_t r = pivotCols.size(); r < m; ++r) {
        if (!isZeroLinalg(c, aug.at(r, n), budget))
            return SymMatrix();
    }

    SymMatrix x = SymMatrix::zeros(c, n, 1);
    for (std::size_t k = 0; k < pivotCols.size(); ++k)
        x.at(pivotCols[k], 0) = aug.at(k, n);
    return x;
}

bool isTriangularMatrix(Ctx &c, const SymMatrix &A, Budget *budget)
{
    const std::size_t n = A.rows();
    bool upper = true;
    bool lower = true;
    for (std::size_t r = 0; r < n; ++r) {
        for (std::size_t col = 0; col < n; ++col) {
            if (r > col && !isZeroLinalg(c, A.at(r, col), budget))
                upper = false;
            if (r < col && !isZeroLinalg(c, A.at(r, col), budget))
                lower = false;
        }
    }
    return upper || lower;
}

bool verifyMatrixExp(Ctx &c, const SymMatrix &A, const SymMatrix &Phi, Expr t,
                     Budget *budget)
{
    const std::size_t n = A.rows();
    if (Phi.rows() != n || Phi.cols() != n)
        return false;
    const SymMatrix dPhi = Phi.diff(c, t);
    const SymMatrix APhi = A.mul(c, Phi);
    const SymMatrix Phi0 = Phi.subs(c, t, c.zero());
    for (std::size_t r = 0; r < n; ++r) {
        for (std::size_t col = 0; col < n; ++col) {
            if (!checkLinalgBudget(c, budget))
                return false;
            const Expr diffEntry =
                c.add({dPhi.at(r, col), c.neg(APhi.at(r, col))});
            if (!isZeroLinalg(c, diffEntry, budget))
                return false;
            const Expr want0 = (r == col) ? c.one() : c.zero();
            if (!isZeroLinalg(c, c.add({Phi0.at(r, col), c.neg(want0)}),
                              budget)) {
                return false;
            }
        }
    }
    return true;
}

} // namespace

std::vector<SymMatrix> nullspace(Ctx &c, const SymMatrix &A, Budget *budget)
{
    if (A.empty())
        return {};
    const std::size_t n = A.cols();
    SymMatrix M = A;
    std::vector<std::size_t> pivotCols;
    if (!computeRREF(c, M, n, pivotCols, budget))
        return {};

    std::vector<bool> isPivot(n, false);
    for (std::size_t pc : pivotCols)
        isPivot[pc] = true;

    std::vector<SymMatrix> basis;
    for (std::size_t freeCol = 0; freeCol < n; ++freeCol) {
        if (isPivot[freeCol])
            continue;
        SymMatrix v = SymMatrix::zeros(c, n, 1);
        v.at(freeCol, 0) = c.one();
        for (std::size_t k = 0; k < pivotCols.size(); ++k) {
            const Expr coef = M.at(k, freeCol);
            if (!c.isZero(coef))
                v.at(pivotCols[k], 0) = normLinalg(c, c.neg(coef), budget);
        }
        basis.push_back(std::move(v));
    }
    return basis;
}

std::vector<EigenPair> eigenvectors(Ctx &c, const SymMatrix &A, Budget *budget)
{
    if (!A.isSquare() || A.empty())
        return {};
    const std::size_t n = A.rows();
    if (!checkLinalgBudget(c, budget))
        return {};

    std::vector<std::pair<Expr, std::size_t>> distinctLams;
    auto addEigenvalue = [&](Expr lam, std::size_t mult) {
        lam = normLinalg(c, lam, budget);
        for (auto &kv : distinctLams) {
            if (isZeroLinalg(c, c.add({kv.first, c.neg(lam)}), budget)) {
                kv.second += mult;
                return;
            }
        }
        distinctLams.push_back({lam, mult});
    };

    if (n == 1) {
        addEigenvalue(A.at(0, 0), 1);
    } else if (isTriangularMatrix(c, A, budget)) {
        for (std::size_t i = 0; i < n; ++i)
            addEigenvalue(A.at(i, i), 1);
    } else {
        const Expr lamSym = c.symbol("_nk_eigen_lambda");
        const Expr cp = charpoly(c, A, lamSym, budget);
        if (cp.isNull())
            return {};

        UPoly up, upDen;
        if (toRational(c, cp, lamSym, up, upDen) && !up.isZero() &&
            upDen.isConst()) {
            const std::vector<UPoly> factors = factorOverQ(up, budget);
            if (budget && !budget->ok())
                return {};
            std::vector<std::pair<UPoly, std::size_t>> grouped;
            for (UPoly f : factors) {
                f.makeMonic();
                bool found = false;
                for (auto &kv : grouped) {
                    if (kv.first == f) {
                        ++kv.second;
                        found = true;
                        break;
                    }
                }
                if (!found)
                    grouped.push_back({f, 1});
            }

            const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
            for (const auto &fe : grouped) {
                const UPoly &P = fe.first;
                const std::size_t mult = fe.second;
                if (P.deg() == 1) {
                    addEigenvalue(c.number(-P.coeff(0)), mult);
                } else if (P.deg() == 2) {
                    const Rational b = P.coeff(1);
                    const Rational c0 = P.coeff(0);
                    const Rational disc = b * b - Rational(std::int64_t{4}) * c0;
                    if (disc.signum() > 0) {
                        const Expr sqrtDisc =
                            simplify(c, c.pow(c.number(disc), half), budget);
                        const Expr negHalfB =
                            c.number(-b / Rational(std::int64_t{2}));
                        const Expr halfSqrt = c.mul({half, sqrtDisc});
                        addEigenvalue(c.add({negHalfB, c.neg(halfSqrt)}), mult);
                        addEigenvalue(c.add({negHalfB, halfSqrt}), mult);
                    }
                } else if (P.deg() >= 3) {
                    const Expr fExpr = upolyToExpr(c, P, lamSym);
                    const std::vector<Expr> roots =
                        solveSymbolic(c, fExpr, lamSym, budget);
                    for (const Expr &r : roots)
                        addEigenvalue(r, mult);
                }
            }
        } else {
            const std::vector<Expr> roots =
                solveSymbolic(c, cp, lamSym, budget);
            for (const Expr &r : roots) {
                // Determine algebraic multiplicity by derivative vanishing order
                std::size_t mult = 0;
                Expr deriv = cp;
                for (std::size_t k = 0; k < n; ++k) {
                    const Expr val = c.subs(deriv, lamSym, r);
                    if (isZeroLinalg(c, val, budget)) {
                        ++mult;
                        deriv = c.diff(deriv, lamSym);
                    } else {
                        break;
                    }
                }
                addEigenvalue(r, mult == 0 ? 1 : mult);
            }
        }
    }

    // Sort eigenvalues deterministically (by numeric value when evaluable, else by string)
    std::sort(distinctLams.begin(), distinctLams.end(),
              [&](const std::pair<Expr, std::size_t> &a,
                  const std::pair<Expr, std::size_t> &b) {
                  double va = 0.0, vb = 0.0;
                  const bool okA = c.evalDouble(a.first, {}, va);
                  const bool okB = c.evalDouble(b.first, {}, vb);
                  if (okA && okB && va != vb)
                      return va < vb;
                  return c.toString(a.first) < c.toString(b.first);
              });

    const SymMatrix I = SymMatrix::eye(c, n);
    std::vector<EigenPair> out;
    out.reserve(distinctLams.size());
    for (const auto &lm : distinctLams) {
        if (!checkLinalgBudget(c, budget))
            return {};
        const SymMatrix shifted = A.sub(c, I.scale(c, lm.first));
        EigenPair ep;
        ep.lambda = lm.first;
        ep.multiplicity = lm.second;
        ep.vectors = nullspace(c, shifted, budget);
        out.push_back(std::move(ep));
    }
    return out;
}

std::vector<Expr> eigenvalues(Ctx &c, const SymMatrix &A, Budget *budget)
{
    const std::vector<EigenPair> pairs = eigenvectors(c, A, budget);
    std::vector<Expr> out;
    for (const auto &ep : pairs) {
        for (std::size_t k = 0; k < ep.multiplicity; ++k)
            out.push_back(ep.lambda);
    }
    return out;
}

SymMatrix matrixExp(Ctx &c, const SymMatrix &A, Expr t, Budget *budget)
{
    if (!A.isSquare() || A.empty() || t.isNull() ||
        c.kind(t) != NodeKind::Symbol) {
        return SymMatrix();
    }
    const std::size_t n = A.rows();
    if (!checkLinalgBudget(c, budget))
        return SymMatrix();

    if (n == 1) {
        SymMatrix out(1, 1);
        out.at(0, 0) = simplify(c, c.func("exp", c.mul({A.at(0, 0), t})), budget);
        if (verifyMatrixExp(c, A, out, t, budget))
            return out;
        return SymMatrix();
    }

    // Path 1: Laplace resolvent inversion Phi(t) = L^{-1}{(s*I - A)^(-1)}(t).
    // Handles all constant matrices over Q (distinct real, repeated/defective
    // Jordan blocks, complex-conjugate pairs alpha +- i*w -> exp*cos/sin, and
    // quadratic real radicals).
    {
        const Expr s = c.symbol("_nk_mat_exp_s");
        const SymMatrix sI = SymMatrix::eye(c, n).scale(c, s);
        const SymMatrix resolvent = inv(c, sI.sub(c, A), budget);
        if (!resolvent.empty()) {
            SymMatrix Phi(n, n, c.zero());
            bool allOk = true;
            for (std::size_t r = 0; r < n && allOk; ++r) {
                for (std::size_t col = 0; col < n && allOk; ++col) {
                    const LaplaceResult lr =
                        ilaplace(c, resolvent.at(r, col), s, t, budget);
                    if (!lr.proved()) {
                        allOk = false;
                        break;
                    }
                    Phi.at(r, col) = lr.F;
                }
            }
            if (allOk && verifyMatrixExp(c, A, Phi, t, budget))
                return Phi;
        }
    }

    // Path 2: Direct Putzer / Cayley-Hamilton closed form for 2x2 symbolic matrices.
    if (n == 2) {
        const SymMatrix I = SymMatrix::eye(c, 2);
        const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
        const Expr alpha =
            normLinalg(c, c.mul({half, A.trace(c)}), budget);
        const Expr detA = det(c, A, budget);
        const Expr delta = normLinalg(
            c, c.add({c.pow(alpha, c.number(std::int64_t{2})), c.neg(detA)}),
            budget);
        const SymMatrix B = A.sub(c, I.scale(c, alpha));
        const Expr expAlphaT = c.func("exp", c.mul({alpha, t}));

        if (isZeroLinalg(c, delta, budget)) {
            // Defective/repeated eigenvalue lambda = alpha:
            // exp(A*t) = exp(alpha*t) * (I + t*(A - alpha*I))
            SymMatrix Phi = I.add(c, B.scale(c, t)).scale(c, expAlphaT);
            for (std::size_t i = 0; i < 4; ++i)
                Phi.at(i / 2, i % 2) =
                    simplify(c, Phi.at(i / 2, i % 2), budget);
            if (verifyMatrixExp(c, A, Phi, t, budget))
                return Phi;
        } else if (c.isAssumedNegative(delta)) {
            const Expr w =
                simplify(c, c.pow(c.neg(delta), half), budget);
            const Expr wt = c.mul({w, t});
            const SymMatrix term1 = I.scale(c, c.func("cos", wt));
            const SymMatrix term2 =
                B.scale(c, c.div(c.func("sin", wt), w));
            SymMatrix Phi = term1.add(c, term2).scale(c, expAlphaT);
            for (std::size_t i = 0; i < 4; ++i)
                Phi.at(i / 2, i % 2) =
                    simplify(c, Phi.at(i / 2, i % 2), budget);
            if (verifyMatrixExp(c, A, Phi, t, budget))
                return Phi;
        } else {
            const Expr mu = simplify(c, c.pow(delta, half), budget);
            const Expr lam1 = normLinalg(c, c.add({alpha, c.neg(mu)}), budget);
            const Expr lam2 = normLinalg(c, c.add({alpha, mu}), budget);
            const Expr e1 = c.func("exp", c.mul({lam1, t}));
            const Expr e2 = c.func("exp", c.mul({lam2, t}));
            const Expr inv2Mu =
                c.pow(c.mul({c.number(std::int64_t{2}), mu}),
                      c.number(std::int64_t{-1}));
            const Expr c0 =
                c.mul({c.add({e1, e2}), half});
            const Expr c1 =
                c.mul({c.add({e2, c.neg(e1)}), inv2Mu});
            SymMatrix Phi = I.scale(c, c0).add(c, B.scale(c, c1));
            for (std::size_t i = 0; i < 4; ++i)
                Phi.at(i / 2, i % 2) =
                    simplify(c, Phi.at(i / 2, i % 2), budget);
            if (verifyMatrixExp(c, A, Phi, t, budget))
                return Phi;
        }
    }

    // Path 3: Spectral / Jordan chain fundamental matrix Y(t) * Y(0)^(-1)
    // for n x n symbolic matrices (e.g. diagonal, triangular, or symmetric).
    {
        const std::vector<EigenPair> pairs = eigenvectors(c, A, budget);
        const SymMatrix I = SymMatrix::eye(c, n);
        std::vector<SymMatrix> cols;
        for (const auto &ep : pairs) {
            const Expr expLamT = c.func("exp", c.mul({ep.lambda, t}));
            const SymMatrix N = A.sub(c, I.scale(c, ep.lambda));
            for (const SymMatrix &v0 : ep.vectors) {
                cols.push_back(v0.scale(c, expLamT));
                // If geometric multiplicity < algebraic multiplicity, build
                // generalized Jordan chain (A - lam*I) w_k = w_{k-1}.
                SymMatrix prev = v0;
                std::vector<SymMatrix> chain = {v0};
                while (cols.size() < n && chain.size() < ep.multiplicity) {
                    const SymMatrix w = linsolveParticular(c, N, prev, budget);
                    if (w.empty())
                        break;
                    chain.push_back(w);
                    prev = w;
                    // Column is exp(lam*t) * sum_{j=0}^{k} t^(k-j)/(k-j)! * chain[j]
                    const std::size_t k = chain.size() - 1;
                    SymMatrix colSum = SymMatrix::zeros(c, n, 1);
                    std::int64_t fact = 1;
                    for (std::size_t d = 0; d <= k; ++d) {
                        if (d > 1)
                            fact *= static_cast<std::int64_t>(d);
                        const Expr tFactor =
                            (d == 0)
                                ? c.one()
                                : c.mul({c.number(Rational(std::int64_t{1},
                                                           BigInt(fact))),
                                         c.pow(t, c.number(
                                                      static_cast<std::int64_t>(
                                                          d)))});
                        colSum = colSum.add(
                            c, chain[k - d].scale(c, tFactor));
                    }
                    cols.push_back(colSum.scale(c, expLamT));
                }
            }
        }
        if (cols.size() == n) {
            SymMatrix Y(n, n, c.zero());
            for (std::size_t r = 0; r < n; ++r)
                for (std::size_t col = 0; col < n; ++col)
                    Y.at(r, col) = cols[col].at(r, 0);
            const SymMatrix Y0 = Y.subs(c, t, c.zero());
            const SymMatrix Y0Inv = inv(c, Y0, budget);
            if (!Y0Inv.empty()) {
                SymMatrix Phi = Y.mul(c, Y0Inv);
                for (std::size_t r = 0; r < n; ++r)
                    for (std::size_t col = 0; col < n; ++col)
                        Phi.at(r, col) = simplify(c, Phi.at(r, col), budget);
                if (verifyMatrixExp(c, A, Phi, t, budget))
                    return Phi;
            }
        }
    }

    return SymMatrix();
}

SymMatrix rref(Ctx &c, const SymMatrix &A,
               std::vector<std::size_t> *pivotColsOut, Budget *budget)
{
    if (A.empty()) {
        if (pivotColsOut)
            pivotColsOut->clear();
        return SymMatrix();
    }
    SymMatrix M = A;
    std::vector<std::size_t> pivotCols;
    if (!computeRREF(c, M, A.cols(), pivotCols, budget))
        return SymMatrix();
    if (pivotColsOut)
        *pivotColsOut = std::move(pivotCols);
    return M;
}

std::size_t rank(Ctx &c, const SymMatrix &A, Budget *budget)
{
    if (A.empty())
        return 0;
    SymMatrix M = A;
    std::vector<std::size_t> pivotCols;
    if (!computeRREF(c, M, A.cols(), pivotCols, budget))
        return 0;
    return pivotCols.size();
}

LUDecomposition lu(Ctx &c, const SymMatrix &A, Budget *budget)
{
    LUDecomposition out;
    if (A.empty()) {
        out.reason = "empty matrix in lu";
        return out;
    }
    const std::size_t m = A.rows();
    const std::size_t n = A.cols();
    if (!checkLinalgBudget(c, budget)) {
        out.reason = "budget exhausted in lu";
        return out;
    }

    SymMatrix U = A;
    for (std::size_t r = 0; r < m; ++r)
        for (std::size_t j = 0; j < n; ++j)
            U.at(r, j) = normLinalg(c, U.at(r, j), budget);

    SymMatrix L = SymMatrix::zeros(c, m, m);
    std::vector<std::size_t> perm(m);
    for (std::size_t i = 0; i < m; ++i)
        perm[i] = i;
    int sign = 1;

    const std::size_t steps = std::min(m, n);
    for (std::size_t k = 0; k < steps; ++k) {
        if (!checkLinalgBudget(c, budget)) {
            out.reason = "budget exhausted in lu";
            return out;
        }
        std::size_t pivotRow = m;
        std::size_t bestCost = static_cast<std::size_t>(-1);
        for (std::size_t r = k; r < m; ++r) {
            const Expr cand = U.at(r, k);
            if (!isZeroLinalg(c, cand, budget)) {
                const std::size_t cost = c.exprCost(cand);
                if (cost < bestCost) {
                    bestCost = cost;
                    pivotRow = r;
                }
            } else {
                U.at(r, k) = c.zero();
            }
        }
        if (pivotRow == m)
            continue;

        if (pivotRow != k) {
            for (std::size_t j = 0; j < n; ++j)
                std::swap(U.at(k, j), U.at(pivotRow, j));
            for (std::size_t j = 0; j < k; ++j)
                std::swap(L.at(k, j), L.at(pivotRow, j));
            std::swap(perm[k], perm[pivotRow]);
            sign = -sign;
        }

        const Expr pivot = U.at(k, k);
        const Expr invPivot = c.pow(pivot, c.number(std::int64_t{-1}));

        for (std::size_t r = k + 1; r < m; ++r) {
            if (!checkLinalgBudget(c, budget)) {
                out.reason = "budget exhausted in lu";
                return out;
            }
            const Expr entry = U.at(r, k);
            if (isZeroLinalg(c, entry, budget)) {
                U.at(r, k) = c.zero();
                L.at(r, k) = c.zero();
                continue;
            }
            L.at(r, k) = normLinalg(c, c.mul({entry, invPivot}), budget);
            U.at(r, k) = c.zero();
            for (std::size_t j = k + 1; j < n; ++j) {
                const Expr crossNum = c.expand(
                    c.add({c.mul({pivot, U.at(r, j)}),
                           c.neg(c.mul({entry, U.at(k, j)}))}));
                if (isZeroLinalg(c, crossNum, budget)) {
                    U.at(r, j) = c.zero();
                } else {
                    U.at(r, j) =
                        normLinalg(c, c.mul({crossNum, invPivot}), budget);
                }
            }
        }
    }

    for (std::size_t i = 0; i < m; ++i)
        L.at(i, i) = c.one();

    SymMatrix P = SymMatrix::zeros(c, m, m);
    for (std::size_t i = 0; i < m; ++i)
        P.at(i, perm[i]) = c.one();

    // Certificate: verify P * A == L * U, L unit lower-triangular, U upper-triangular.
    const SymMatrix PA = P.mul(c, A);
    const SymMatrix LU = L.mul(c, U);
    for (std::size_t r = 0; r < m; ++r) {
        for (std::size_t j = 0; j < m; ++j) {
            if (r < j && !isZeroLinalg(c, L.at(r, j), budget)) {
                out.reason = "L is not lower triangular";
                return out;
            }
            if (r == j &&
                !isZeroLinalg(c, c.add({L.at(r, j), c.neg(c.one())}), budget)) {
                out.reason = "L is not unit diagonal";
                return out;
            }
        }
        for (std::size_t j = 0; j < n; ++j) {
            if (!checkLinalgBudget(c, budget)) {
                out.reason = "budget exhausted during lu verification";
                return out;
            }
            if (r > j && !isZeroLinalg(c, U.at(r, j), budget)) {
                out.reason = "U is not upper triangular";
                return out;
            }
            const Expr diffEntry = c.add({PA.at(r, j), c.neg(LU.at(r, j))});
            if (!isZeroLinalg(c, diffEntry, budget)) {
                out.reason = "LU decomposition certificate P*A == L*U failed";
                return out;
            }
        }
    }

    out.L = std::move(L);
    out.U = std::move(U);
    out.P = std::move(P);
    out.perm = std::move(perm);
    out.sign = sign;
    out.status = LUDecomposition::Status::ProvedSymbolic;
    return out;
}

namespace {

Expr dotCols(Ctx &c, const SymMatrix &u, const SymMatrix &v, Budget *budget)
{
    std::vector<Expr> terms;
    terms.reserve(u.rows());
    for (std::size_t r = 0; r < u.rows(); ++r)
        terms.push_back(c.mul({u.at(r, 0), v.at(r, 0)}));
    return normLinalg(c, terms.empty() ? c.zero() : c.add(terms), budget);
}

} // namespace

std::vector<SymMatrix> gramSchmidt(Ctx &c, const std::vector<SymMatrix> &cols,
                                   bool normalize, Budget *budget)
{
    if (cols.empty())
        return {};
    const std::size_t m = cols[0].rows();
    if (m == 0)
        return {};
    for (const auto &v : cols) {
        if (v.rows() != m || v.cols() != 1)
            return {};
    }

    std::vector<SymMatrix> orthoCols;
    std::vector<Expr> normSq;
    for (const auto &a : cols) {
        if (!checkLinalgBudget(c, budget))
            return {};
        SymMatrix u = a;
        for (std::size_t i = 0; i < orthoCols.size(); ++i) {
            const Expr projNum = dotCols(c, orthoCols[i], a, budget);
            if (isZeroLinalg(c, projNum, budget))
                continue;
            const Expr coeff =
                normLinalg(c, c.div(projNum, normSq[i]), budget);
            u = u.sub(c, orthoCols[i].scale(c, coeff));
        }
        for (std::size_t r = 0; r < m; ++r)
            u.at(r, 0) = normLinalg(c, u.at(r, 0), budget);
        const Expr d = dotCols(c, u, u, budget);
        if (isZeroLinalg(c, d, budget))
            continue; // linearly dependent column
        orthoCols.push_back(std::move(u));
        normSq.push_back(d);
    }

    if (!normalize)
        return orthoCols;

    const Expr negHalf = c.number(Rational(std::int64_t{-1}, BigInt(2)));
    std::vector<SymMatrix> out;
    out.reserve(orthoCols.size());
    for (std::size_t i = 0; i < orthoCols.size(); ++i) {
        if (c.isAssumedNegative(normSq[i]))
            return {};
        const Expr invNorm =
            simplify(c, c.pow(normSq[i], negHalf), budget);
        SymMatrix q = orthoCols[i].scale(c, invNorm);
        for (std::size_t r = 0; r < m; ++r)
            q.at(r, 0) = simplify(c, q.at(r, 0), budget);
        out.push_back(std::move(q));
    }
    return out;
}

QRDecomposition qr(Ctx &c, const SymMatrix &A, Budget *budget)
{
    QRDecomposition out;
    if (A.empty() || A.rows() < A.cols()) {
        out.reason = "qr requires non-empty matrix with rows >= cols";
        return out;
    }
    const std::size_t m = A.rows();
    const std::size_t n = A.cols();

    std::vector<SymMatrix> aCols(n, SymMatrix(m, 1, c.zero()));
    for (std::size_t j = 0; j < n; ++j)
        for (std::size_t r = 0; r < m; ++r)
            aCols[j].at(r, 0) = normLinalg(c, A.at(r, j), budget);

    // Unnormalized Gram-Schmidt basis u_0, ..., u_{n-1} and squared norms d_i = <u_i, u_i>.
    std::vector<SymMatrix> uCols;
    std::vector<Expr> dNorms;
    SymMatrix projMat = SymMatrix::zeros(c, n, n); // projMat(i, j) = <u_i, a_j> for i < j

    for (std::size_t j = 0; j < n; ++j) {
        if (!checkLinalgBudget(c, budget)) {
            out.reason = "budget exhausted in qr";
            return out;
        }
        SymMatrix u = aCols[j];
        for (std::size_t i = 0; i < j; ++i) {
            const Expr ip = dotCols(c, uCols[i], aCols[j], budget);
            projMat.at(i, j) = ip;
            if (!isZeroLinalg(c, ip, budget)) {
                const Expr coeff = normLinalg(c, c.div(ip, dNorms[i]), budget);
                u = u.sub(c, uCols[i].scale(c, coeff));
            }
        }
        for (std::size_t r = 0; r < m; ++r)
            u.at(r, 0) = normLinalg(c, u.at(r, 0), budget);
        const Expr d = dotCols(c, u, u, budget);
        if (isZeroLinalg(c, d, budget) || c.isAssumedNegative(d)) {
            out.reason = "columns of A are linearly dependent or have non-positive norm";
            return out;
        }
        uCols.push_back(std::move(u));
        dNorms.push_back(d);
    }

    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
    const Expr negHalf = c.number(Rational(std::int64_t{-1}, BigInt(2)));
    SymMatrix Q = SymMatrix::zeros(c, m, n);
    SymMatrix R = SymMatrix::zeros(c, n, n);

    for (std::size_t i = 0; i < n; ++i) {
        const Expr sqrtDi = simplify(c, c.pow(dNorms[i], half), budget);
        const Expr invSqrtDi = simplify(c, c.pow(dNorms[i], negHalf), budget);
        R.at(i, i) = sqrtDi;
        for (std::size_t r = 0; r < m; ++r)
            Q.at(r, i) = simplify(c, c.mul({uCols[i].at(r, 0), invSqrtDi}), budget);
        for (std::size_t j = i + 1; j < n; ++j) {
            if (!c.isZero(projMat.at(i, j))) {
                R.at(i, j) =
                    simplify(c, c.mul({projMat.at(i, j), invSqrtDi}), budget);
            }
        }
    }

    // Certificate: verify Q * R == A and Q^T * Q == I_n.
    const SymMatrix QR = Q.mul(c, R);
    for (std::size_t r = 0; r < m; ++r) {
        for (std::size_t j = 0; j < n; ++j) {
            if (!checkLinalgBudget(c, budget)) {
                out.reason = "budget exhausted during qr verification";
                return out;
            }
            if (!isZeroLinalg(c, c.add({QR.at(r, j), c.neg(A.at(r, j))}),
                              budget)) {
                out.reason = "QR decomposition certificate Q*R == A failed";
                return out;
            }
        }
    }
    const SymMatrix QtQ = Q.transpose().mul(c, Q);
    for (std::size_t i = 0; i < n; ++i) {
        for (std::size_t j = 0; j < n; ++j) {
            const Expr want = (i == j) ? c.one() : c.zero();
            if (!isZeroLinalg(c, c.add({QtQ.at(i, j), c.neg(want)}), budget)) {
                out.reason = "QR decomposition certificate Q^T*Q == I failed";
                return out;
            }
        }
    }

    out.Q = std::move(Q);
    out.R = std::move(R);
    out.status = QRDecomposition::Status::ProvedSymbolic;
    return out;
}

namespace {

bool isColIndependentOf(Ctx &c, const std::vector<SymMatrix> &existingCols,
                        const SymMatrix &cand, Budget *budget)
{
    const std::size_t n = cand.rows();
    bool allZero = true;
    for (std::size_t r = 0; r < n; ++r) {
        if (!isZeroLinalg(c, cand.at(r, 0), budget)) {
            allZero = false;
            break;
        }
    }
    if (allZero)
        return false;
    if (existingCols.empty())
        return true;

    const std::size_t k = existingCols.size();
    SymMatrix M(n, k + 1, c.zero());
    for (std::size_t j = 0; j < k; ++j)
        for (std::size_t r = 0; r < n; ++r)
            M.at(r, j) = existingCols[j].at(r, 0);
    for (std::size_t r = 0; r < n; ++r)
        M.at(r, k) = cand.at(r, 0);

    std::vector<std::size_t> pivs;
    if (!computeRREF(c, M, k + 1, pivs, budget))
        return false;
    return !pivs.empty() && pivs.back() == k;
}

} // namespace

JordanDecomposition jordanForm(Ctx &c, const SymMatrix &A, Budget *budget)
{
    JordanDecomposition out;
    if (A.empty() || !A.isSquare()) {
        out.reason = "jordanForm requires a non-empty square matrix";
        return out;
    }
    const std::size_t n = A.rows();
    if (!checkLinalgBudget(c, budget)) {
        out.reason = "budget exhausted in jordanForm";
        return out;
    }

    const std::vector<EigenPair> pairs = eigenvectors(c, A, budget);
    std::size_t totalMult = 0;
    for (const auto &ep : pairs)
        totalMult += ep.multiplicity;
    if (totalMult != n) {
        out.reason = "eigenvalues of A do not split over the supported radical domain";
        return out;
    }

    const SymMatrix I = SymMatrix::eye(c, n);
    SymMatrix J = SymMatrix::zeros(c, n, n);
    std::vector<SymMatrix> pCols;
    pCols.reserve(n);

    for (const auto &ep : pairs) {
        const Expr lam = ep.lambda;
        const std::size_t algMult = ep.multiplicity;
        const std::size_t geomMult = ep.vectors.size();
        if (geomMult == 0) {
            out.reason = "empty eigenspace for eigenvalue in jordanForm";
            return out;
        }

        // Fast path: non-defective eigenvalue (geometric == algebraic multiplicity).
        if (geomMult == algMult) {
            for (const SymMatrix &v : ep.vectors) {
                const std::size_t idx = pCols.size();
                J.at(idx, idx) = lam;
                pCols.push_back(v);
            }
            continue;
        }

        // Defective eigenvalue: build powers N^1, ..., N^r of N = A - lam * I
        // until nullity(N^r) == algMult, then extract Jordan chains from top
        // block size k = r down to k = 1.
        const SymMatrix N = A.sub(c, I.scale(c, lam));
        std::vector<SymMatrix> nPows;
        nPows.push_back(I); // N^0
        nPows.push_back(N); // N^1
        std::vector<std::vector<SymMatrix>> kerBases(2);
        kerBases[1] = ep.vectors;

        std::size_t maxK = 1;
        while (kerBases[maxK].size() < algMult && maxK < algMult) {
            if (!checkLinalgBudget(c, budget)) {
                out.reason = "budget exhausted computing nilpotent powers";
                return out;
            }
            const SymMatrix nextPow = nPows.back().mul(c, N);
            nPows.push_back(nextPow);
            kerBases.push_back(nullspace(c, nextPow, budget));
            ++maxK;
        }
        if (kerBases[maxK].size() < algMult) {
            out.reason = "generalized eigenspace dimension smaller than algebraic multiplicity";
            return out;
        }

        std::vector<SymMatrix> bottomVecs; // linearly independent cycle bottoms in ker(N)
        std::size_t collectedForLam = 0;

        for (std::size_t k = maxK; k >= 1 && collectedForLam < algMult; --k) {
            for (const SymMatrix &w : kerBases[k]) {
                if (collectedForLam + k > algMult)
                    break;
                // Bottom of the length-k chain generated by w is b = N^(k-1) * w in ker(N).
                const SymMatrix b = (k == 1) ? w : nPows[k - 1].mul(c, w);
                if (!isColIndependentOf(c, bottomVecs, b, budget))
                    continue;
                bottomVecs.push_back(b);

                // Emit the k-vector Jordan chain:
                // v_1 = N^(k-1)*w, v_2 = N^(k-2)*w, ..., v_k = w
                // satisfying (A - lam*I)*v_1 = 0 and (A - lam*I)*v_j = v_{j-1}.
                const std::size_t blockStart = pCols.size();
                for (std::size_t step = 0; step < k; ++step) {
                    const std::size_t powIdx = k - 1 - step;
                    SymMatrix vj = (powIdx == 0) ? w : nPows[powIdx].mul(c, w);
                    for (std::size_t r = 0; r < n; ++r)
                        vj.at(r, 0) = normLinalg(c, vj.at(r, 0), budget);
                    const std::size_t colIdx = blockStart + step;
                    J.at(colIdx, colIdx) = lam;
                    if (step + 1 < k)
                        J.at(colIdx, colIdx + 1) = c.one();
                    pCols.push_back(std::move(vj));
                }
                collectedForLam += k;
            }
        }

        if (collectedForLam != algMult) {
            out.reason = "failed to construct complete Jordan chains for eigenvalue";
            return out;
        }
    }

    if (pCols.size() != n) {
        out.reason = "incomplete Jordan basis";
        return out;
    }

    SymMatrix P(n, n, c.zero());
    for (std::size_t j = 0; j < n; ++j)
        for (std::size_t r = 0; r < n; ++r)
            P.at(r, j) = pCols[j].at(r, 0);

    SymMatrix PInv = inv(c, P, budget);
    if (PInv.empty()) {
        out.reason = "Jordan basis matrix P is singular";
        return out;
    }

    // Certificate: verify A * P == P * J and P * PInv == I_n.
    const SymMatrix AP = A.mul(c, P);
    const SymMatrix PJ = P.mul(c, J);
    const SymMatrix PPInv = P.mul(c, PInv);
    for (std::size_t r = 0; r < n; ++r) {
        for (std::size_t j = 0; j < n; ++j) {
            if (!checkLinalgBudget(c, budget)) {
                out.reason = "budget exhausted during jordanForm verification";
                return out;
            }
            if (!isZeroLinalg(c, c.add({AP.at(r, j), c.neg(PJ.at(r, j))}),
                              budget)) {
                out.reason = "Jordan certificate A*P == P*J failed";
                return out;
            }
            const Expr wantI = (r == j) ? c.one() : c.zero();
            if (!isZeroLinalg(c, c.add({PPInv.at(r, j), c.neg(wantI)}),
                              budget)) {
                out.reason = "Jordan certificate P*PInv == I failed";
                return out;
            }
        }
    }

    out.J = std::move(J);
    out.P = std::move(P);
    out.PInv = std::move(PInv);
    out.status = JordanDecomposition::Status::ProvedSymbolic;
    return out;
}

} // namespace numkit::cas
