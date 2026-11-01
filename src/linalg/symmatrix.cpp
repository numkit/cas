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

FormalFrac toFormalFrac(Ctx &c, Expr e, bool splitFracPow = false)
{
    if (e.isNull())
        return {Expr(), Expr()};
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return {e, c.one()};
    case NodeKind::Func: {
        std::vector<Expr> args;
        args.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr arg = simplifyRationalExpr(c, c.child(e, i));
            if (arg.isNull())
                return {Expr(), Expr()};
            args.push_back(arg);
        }
        const Expr fn = c.func(c.funcName(e), args);
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
                const FormalFrac bf = toFormalFrac(c, b, splitFracPow);
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
            if (splitFracPow && rv.den() > BigInt(1)) {
                BigInt kBig = rv.num() / rv.den();
                BigInt rBig = rv.num() % rv.den();
                if (rBig.signum() < 0) {
                    kBig = kBig - BigInt(1);
                    rBig = rBig + rv.den();
                }
                std::int64_t kFloor = 0;
                if (kBig.fitsInt64(kFloor) && std::abs(kFloor) <= 16) {
                    const Expr sb = simplifyRationalExpr(c, b);
                    if (sb.isNull() || c.isZero(sb))
                        return {Expr(), Expr()};
                    const Expr rad =
                        c.pow(sb, c.number(Rational(rBig, rv.den())));
                    if (kFloor == 0)
                        return {rad, c.one()};
                    if (kFloor > 0) {
                        return {c.expand(c.mul(
                                    {rad, c.expand(c.pow(sb, c.number(kFloor)))})),
                                c.one()};
                    }
                    return {rad, c.expand(c.pow(sb, c.number(-kFloor)))};
                }
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
            const FormalFrac cf = toFormalFrac(c, c.child(e, i), splitFracPow);
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
            const FormalFrac cf = toFormalFrac(c, c.child(e, i), splitFracPow);
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

bool extractPolyCoeffsInSym(Ctx &c, Expr e, Expr var,
                            std::vector<Expr> &coeffsOut)
{
    const Expr expd = c.expand(e);
    std::vector<Expr> terms;
    if (c.kind(expd) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(expd); ++i)
            terms.push_back(c.child(expd, i));
    } else {
        terms.push_back(expd);
    }

    int maxDeg = 0;
    std::vector<std::pair<int, Expr>> parsed;
    parsed.reserve(terms.size());
    for (const Expr &t : terms) {
        if (c.isZero(t))
            continue;
        int deg = 0;
        std::vector<Expr> rest;
        auto inspect = [&](Expr f) -> bool {
            if (f == var) {
                deg += 1;
                return true;
            }
            if (c.kind(f) == NodeKind::Pow && c.child(f, 0) == var &&
                c.kind(c.child(f, 1)) == NodeKind::Number) {
                const Rational &rv = c.numberValue(c.child(f, 1));
                std::int64_t k = 0;
                if (rv.den() == BigInt(1) && rv.num().fitsInt64(k) && k >= 0 &&
                    k <= 24) {
                    deg += static_cast<int>(k);
                    return true;
                }
                return false;
            }
            rest.push_back(f);
            return true;
        };
        if (c.kind(t) == NodeKind::Mul) {
            for (std::size_t i = 0; i < c.childCount(t); ++i) {
                if (!inspect(c.child(t, i)))
                    return false;
            }
        } else {
            if (!inspect(t))
                return false;
        }
        if (deg > 24)
            return false;
        maxDeg = std::max(maxDeg, deg);
        parsed.emplace_back(deg, rest.empty() ? c.one() : c.mul(rest));
    }

    coeffsOut.assign(static_cast<std::size_t>(maxDeg + 1), c.zero());
    for (const auto &pr : parsed) {
        const std::size_t idx = static_cast<std::size_t>(pr.first);
        coeffsOut[idx] = c.expand(c.add({coeffsOut[idx], pr.second}));
    }
    while (!coeffsOut.empty() && c.isZero(coeffsOut.back()))
        coeffsOut.pop_back();
    return true;
}

bool polyDivExactMulti(Ctx &c, Expr P, Expr Q, const std::vector<Expr> &syms,
                       std::size_t symIdx, Expr &quotOut)
{
    if (c.isZero(Q))
        return false;
    if (c.isZero(P)) {
        quotOut = c.zero();
        return true;
    }
    if (P == Q) {
        quotOut = c.one();
        return true;
    }
    if (symIdx >= syms.size()) {
        if (c.kind(P) == NodeKind::Number && c.kind(Q) == NodeKind::Number) {
            quotOut = c.number(c.numberValue(P) / c.numberValue(Q));
            return true;
        }
        return false;
    }

    const Expr var = syms[symIdx];
    std::vector<Expr> pCoeffs, qCoeffs;
    if (!extractPolyCoeffsInSym(c, P, var, pCoeffs) ||
        !extractPolyCoeffsInSym(c, Q, var, qCoeffs) || qCoeffs.empty())
        return false;

    if (pCoeffs.empty()) {
        quotOut = c.zero();
        return true;
    }

    const int degP = static_cast<int>(pCoeffs.size()) - 1;
    const int degQ = static_cast<int>(qCoeffs.size()) - 1;
    if (degP < degQ)
        return false;

    if (degQ == 0) {
        std::vector<Expr> terms;
        for (int k = 0; k <= degP; ++k) {
            if (c.isZero(pCoeffs[static_cast<std::size_t>(k)]))
                continue;
            Expr qk;
            if (!polyDivExactMulti(c, pCoeffs[static_cast<std::size_t>(k)],
                                   qCoeffs[0], syms, symIdx + 1, qk))
                return false;
            const Expr vPow =
                (k == 0)
                    ? c.one()
                    : (k == 1
                           ? var
                           : c.pow(var, c.number(static_cast<std::int64_t>(k))));
            terms.push_back(c.mul({qk, vPow}));
        }
        quotOut = terms.empty() ? c.zero() : c.expand(c.add(terms));
        return true;
    }

    Expr R = P;
    std::vector<Expr> qTerms;
    for (int step = 0; step <= degP - degQ + 1; ++step) {
        std::vector<Expr> rCoeffs;
        if (!extractPolyCoeffsInSym(c, R, var, rCoeffs))
            return false;
        if (rCoeffs.empty()) {
            quotOut = qTerms.empty() ? c.zero() : c.expand(c.add(qTerms));
            return true;
        }
        const int degR = static_cast<int>(rCoeffs.size()) - 1;
        if (degR < degQ)
            return false;
        Expr lcQuot;
        if (!polyDivExactMulti(c, rCoeffs[static_cast<std::size_t>(degR)],
                               qCoeffs[static_cast<std::size_t>(degQ)], syms,
                               symIdx + 1, lcQuot))
            return false;
        const int dDiff = degR - degQ;
        const Expr vPow =
            (dDiff == 0)
                ? c.one()
                : (dDiff == 1
                       ? var
                       : c.pow(var,
                               c.number(static_cast<std::int64_t>(dDiff))));
        const Expr term = c.expand(c.mul({lcQuot, vPow}));
        qTerms.push_back(term);
        R = c.expand(c.add({R, c.neg(c.mul({term, Q}))}));
    }
    return false;
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
        if (!combined.isNull() && toRational(c, combined, syms[0], upN, upD) &&
            !upD.isZero()) {
            const UPoly g = UPoly::gcd(upN, upD);
            if (!g.isConst()) {
                UPoly remG;
                UPoly::divMod(upN, g, upN, remG);
                UPoly::divMod(upD, g, upD, remG);
            }
            const Rational lcD = upD.lc();
            upN = upN * (Rational(std::int64_t{1}) / lcD);
            upD.makeMonic();
            const Expr rN = upolyToExpr(c, upN, syms[0]);
            if (upD.isConst())
                return rN;
            const Expr rD = upolyToExpr(c, upD, syms[0]);
            return c.div(rN, rD);
        }
    } else if (pureRat && syms.size() >= 2 && syms.size() <= 6) {
        Expr quot;
        if (polyDivExactMulti(c, f.num, f.den, syms, 0, quot))
            return quot;
        if (polyDivExactMulti(c, f.den, f.num, syms, 0, quot) &&
            !c.isZero(quot))
            return c.pow(quot, c.number(std::int64_t{-1}));
    } else if (!pureRat && c.kind(e) == NodeKind::Add) {
        const FormalFrac fRad = toFormalFrac(c, e, true);
        if (!fRad.num.isNull() && !fRad.den.isNull() &&
            !c.isZero(fRad.den) && c.isZero(fRad.num)) {
            return c.zero();
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

Expr divergence(Ctx &c, const std::vector<Expr> &F,
                const std::vector<Expr> &vars)
{
    if (F.empty() || F.size() != vars.size())
        return Expr{};
    std::vector<Expr> terms;
    terms.reserve(F.size());
    for (std::size_t i = 0; i < F.size(); ++i) {
        if (F[i].isNull() || vars[i].isNull() ||
            c.kind(vars[i]) != NodeKind::Symbol) {
            return Expr{};
        }
        const Expr dFi = c.diff(F[i], vars[i]);
        if (dFi.isNull())
            return Expr{};
        terms.push_back(dFi);
    }
    return c.simplify(simplifyRationalExpr(c, c.add(terms)));
}

SymMatrix curl(Ctx &c, const std::vector<Expr> &F,
               const std::vector<Expr> &vars)
{
    if (F.size() != 3 || vars.size() != 3)
        return SymMatrix{};
    for (std::size_t i = 0; i < 3; ++i) {
        if (F[i].isNull() || vars[i].isNull() ||
            c.kind(vars[i]) != NodeKind::Symbol) {
            return SymMatrix{};
        }
    }
    const Expr dF2y = c.diff(F[2], vars[1]);
    const Expr dF1z = c.diff(F[1], vars[2]);
    const Expr dF0z = c.diff(F[0], vars[2]);
    const Expr dF2x = c.diff(F[2], vars[0]);
    const Expr dF1x = c.diff(F[1], vars[0]);
    const Expr dF0y = c.diff(F[0], vars[1]);
    if (dF2y.isNull() || dF1z.isNull() || dF0z.isNull() || dF2x.isNull() ||
        dF1x.isNull() || dF0y.isNull()) {
        return SymMatrix{};
    }
    SymMatrix out(3, 1);
    out.at(0, 0) =
        c.simplify(simplifyRationalExpr(c, c.add({dF2y, c.neg(dF1z)})));
    out.at(1, 0) =
        c.simplify(simplifyRationalExpr(c, c.add({dF0z, c.neg(dF2x)})));
    out.at(2, 0) =
        c.simplify(simplifyRationalExpr(c, c.add({dF1x, c.neg(dF0y)})));
    return out;
}

Expr laplacian(Ctx &c, Expr f, const std::vector<Expr> &vars)
{
    if (f.isNull() || vars.empty())
        return Expr{};
    std::vector<Expr> terms;
    terms.reserve(vars.size());
    for (const Expr &v : vars) {
        if (v.isNull() || c.kind(v) != NodeKind::Symbol)
            return Expr{};
        const Expr d1 = c.diff(f, v);
        if (d1.isNull())
            return Expr{};
        const Expr d2 = c.diff(d1, v);
        if (d2.isNull())
            return Expr{};
        terms.push_back(d2);
    }
    return c.simplify(simplifyRationalExpr(c, c.add(terms)));
}

SymMatrix wronskianMatrix(Ctx &c, const std::vector<Expr> &funcs, Expr var)
{
    if (funcs.empty() || var.isNull() || c.kind(var) != NodeKind::Symbol)
        return SymMatrix{};
    const std::size_t n = funcs.size();
    SymMatrix W(n, n);
    for (std::size_t j = 0; j < n; ++j) {
        if (funcs[j].isNull())
            return SymMatrix{};
        Expr cur = funcs[j];
        W.at(0, j) = cur;
        for (std::size_t i = 1; i < n; ++i) {
            cur = c.diff(cur, var);
            if (cur.isNull())
                return SymMatrix{};
            W.at(i, j) = c.simplify(cur);
        }
    }
    return W;
}

Expr wronskian(Ctx &c, const std::vector<Expr> &funcs, Expr var,
               Budget *budget)
{
    const SymMatrix W = wronskianMatrix(c, funcs, var);
    if (W.empty())
        return Expr{};
    const Expr d = det(c, W, budget);
    if (d.isNull())
        return Expr{};
    return simplify(c, d, budget);
}

namespace {

bool mentionsVarLinalg(const Ctx &c, Expr e, Expr var)
{
    if (e.isNull())
        return false;
    if (e == var)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i) {
        if (mentionsVarLinalg(c, c.child(e, i), var))
            return true;
    }
    return false;
}

bool isZeroLinalg(Ctx &c, Expr e)
{
    if (e.isNull())
        return false;
    if (c.isZero(e))
        return true;
    const Expr r = simplifyRationalExpr(c, e);
    if (!r.isNull() && c.isZero(r))
        return true;
    const Expr s = c.simplify(e);
    if (c.isZero(s))
        return true;
    const Expr sr = simplifyRationalExpr(c, s);
    return !sr.isNull() && c.isZero(sr);
}

} // namespace

PotentialResult scalarPotential(Ctx &c, const std::vector<Expr> &F,
                                const std::vector<Expr> &vars,
                                Budget *budget)
{
    PotentialResult out;
    if (F.empty() || F.size() != vars.size()) {
        out.reason = "invalid vector field or variable dimensions";
        return out;
    }
    const std::size_t n = F.size();
    for (std::size_t i = 0; i < n; ++i) {
        if (F[i].isNull() || vars[i].isNull() ||
            c.kind(vars[i]) != NodeKind::Symbol) {
            out.reason = "invalid component or variable symbol";
            return out;
        }
    }
    if (!checkLinalgBudget(c, budget)) {
        out.reason = "budget exhausted";
        return out;
    }

    // 1. Check conservative / curl-free integrability conditions:
    //    dF_i / dx_j == dF_j / dx_i for all 0 <= i < j < n.
    for (std::size_t i = 0; i < n; ++i) {
        for (std::size_t j = i + 1; j < n; ++j) {
            const Expr dFi = c.diff(F[i], vars[j]);
            const Expr dFj = c.diff(F[j], vars[i]);
            if (dFi.isNull() || dFj.isNull() ||
                !isZeroLinalg(c, c.add({dFi, c.neg(dFj)}))) {
                out.reason =
                    "vector field is not conservative (dF_i/dx_j != dF_j/dx_i)";
                return out;
            }
        }
    }

    // 2. Sequential line integration along coordinate axes.
    Expr phi = c.zero();
    for (std::size_t i = 0; i < n; ++i) {
        if (!checkLinalgBudget(c, budget)) {
            out.reason = "budget exhausted";
            return out;
        }
        const Expr dPhi = c.diff(phi, vars[i]);
        if (dPhi.isNull()) {
            out.reason = "differentiation failed during potential reconstruction";
            return out;
        }
        Expr rem = simplify(c, c.add({F[i], c.neg(dPhi)}), budget);
        for (std::size_t k = 0; k < i; ++k) {
            if (mentionsVarLinalg(c, rem, vars[k])) {
                const Expr ratRem = simplifyRationalExpr(c, rem);
                if (!ratRem.isNull())
                    rem = ratRem;
            }
            if (mentionsVarLinalg(c, rem, vars[k])) {
                out.reason =
                    "residual depends on previously integrated variable";
                return out;
            }
        }
        if (c.isZero(rem))
            continue;
        const RationalIntegral intRem = integrate(c, rem, vars[i], budget);
        if (!intRem.proved()) {
            out.reason = "unable to integrate component: " + intRem.reason;
            return out;
        }
        phi = simplify(c, c.add({phi, intRem.F}), budget);
    }

    // 3. Proof-carrying certificate: verify gradient(phi) == F componentwise.
    for (std::size_t i = 0; i < n; ++i) {
        const Expr dPhi = c.diff(phi, vars[i]);
        if (dPhi.isNull() || !isZeroLinalg(c, c.add({dPhi, c.neg(F[i])}))) {
            out.reason = "scalar potential failed gradient certificate";
            return out;
        }
    }

    out.status = PotentialResult::Status::ProvedSymbolic;
    out.phi = phi;
    return out;
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

namespace {

Expr extractRationalNumerator(Ctx &c, Expr e)
{
    const Expr norm = simplifyRationalExpr(c, e);
    if (norm.isNull())
        return e;
    if (c.kind(norm) == NodeKind::Pow &&
        c.kind(c.child(norm, 1)) == NodeKind::Number &&
        c.numberValue(c.child(norm, 1)).signum() < 0) {
        return c.one();
    }
    if (c.kind(norm) == NodeKind::Mul) {
        std::vector<Expr> numFactors;
        for (std::size_t i = 0; i < c.childCount(norm); ++i) {
            const Expr ch = c.child(norm, i);
            if (c.kind(ch) == NodeKind::Pow &&
                c.kind(c.child(ch, 1)) == NodeKind::Number &&
                c.numberValue(c.child(ch, 1)).signum() < 0) {
                continue;
            }
            numFactors.push_back(ch);
        }
        return numFactors.empty() ? c.one() : c.expand(c.mul(numFactors));
    }
    return c.expand(norm);
}

Expr subsSimultaneousLinalg(Ctx &c, Expr e, const std::vector<Expr> &vars,
                            const std::vector<Expr> &vals)
{
    if (e.isNull())
        return Expr();
    std::vector<Expr> tmps;
    tmps.reserve(vars.size());
    Expr cur = e;
    for (std::size_t i = 0; i < vars.size(); ++i) {
        const Expr tmp = c.symbol("$kkt_tmp_" + std::to_string(i));
        tmps.push_back(tmp);
        cur = c.subs(cur, vars[i], tmp);
    }
    for (std::size_t i = 0; i < vars.size(); ++i)
        cur = c.subs(cur, tmps[i], vals[i]);
    return cur;
}

bool evalExprSign(Ctx &c, Expr e, int &signOut)
{
    if (e.isNull())
        return false;
    const Expr s = c.simplify(e);
    Rational r;
    if (c.evalExact(s, {}, r)) {
        signOut = r.signum();
        return true;
    }
    double d = 0.0;
    if (c.evalDouble(s, {}, d)) {
        if (d > 1e-10)
            signOut = +1;
        else if (d < -1e-10)
            signOut = -1;
        else
            signOut = 0;
        return true;
    }
    return false;
}

int leadingMinorSign(Ctx &c, const SymMatrix &M, std::size_t k, Budget *budget,
                     bool &okOut)
{
    SymMatrix subM(k, k, c.zero());
    for (std::size_t r = 0; r < k; ++r)
        for (std::size_t col = 0; col < k; ++col)
            subM.at(r, col) = M.at(r, col);
    const Expr d = det(c, subM, budget);
    int s = 0;
    okOut = evalExprSign(c, d, s);
    return s;
}

} // namespace

LagrangeExtremaResult lagrangeExtrema(
    Ctx &c, Expr f, const std::vector<Expr> &vars,
    const std::vector<Expr> &constraints, Budget *budget)
{
    LagrangeExtremaResult out;
    if (!checkLinalgBudget(c, budget)) {
        out.reason = "budget exhausted";
        return out;
    }
    if (f.isNull()) {
        out.reason = "null objective function";
        return out;
    }
    if (vars.empty()) {
        out.reason = "empty variable list";
        return out;
    }
    const std::size_t n = vars.size();
    const std::size_t m = constraints.size();
    for (std::size_t i = 0; i < n; ++i) {
        if (vars[i].isNull() || c.kind(vars[i]) != NodeKind::Symbol) {
            out.reason = "decision variables must be symbols";
            return out;
        }
        for (std::size_t j = i + 1; j < n; ++j) {
            if (vars[i] == vars[j]) {
                out.reason = "duplicate decision variable";
                return out;
            }
        }
    }
    for (Expr g : constraints) {
        if (g.isNull()) {
            out.reason = "null constraint expression";
            return out;
        }
    }

    std::vector<Expr> lamVars;
    lamVars.reserve(m);
    for (std::size_t j = 0; j < m; ++j)
        lamVars.push_back(c.symbol("$lam_" + std::to_string(j)));

    // Build KKT stationarity equations dL/dx_i = df/dx_i - sum_j lam_j * dg_j/dx_i = 0
    // and constraint equations g_j(x) = 0.
    std::vector<Expr> kktResiduals;
    std::vector<Expr> polyEqs;
    kktResiduals.reserve(n + m);
    polyEqs.reserve(n + m);

    for (std::size_t i = 0; i < n; ++i) {
        std::vector<Expr> terms{c.diff(f, vars[i])};
        if (terms[0].isNull()) {
            out.reason = "failed to differentiate objective function";
            return out;
        }
        for (std::size_t j = 0; j < m; ++j) {
            const Expr dgj = c.diff(constraints[j], vars[i]);
            if (dgj.isNull()) {
                out.reason = "failed to differentiate constraint";
                return out;
            }
            terms.push_back(c.neg(c.mul({lamVars[j], dgj})));
        }
        const Expr kktEq = c.add(terms);
        kktResiduals.push_back(kktEq);
        polyEqs.push_back(extractRationalNumerator(c, kktEq));
    }
    for (std::size_t j = 0; j < m; ++j) {
        kktResiduals.push_back(constraints[j]);
        polyEqs.push_back(extractRationalNumerator(c, constraints[j]));
    }

    // Solve KKT system via solveSystem. Put multipliers first in Lex order so
    // linear multipliers are eliminated first and coordinates are triangularized.
    std::vector<Expr> solveVars;
    solveVars.reserve(m + n);
    for (Expr lv : lamVars)
        solveVars.push_back(lv);
    for (Expr xv : vars)
        solveVars.push_back(xv);

    std::vector<std::vector<Expr>> rawSols =
        solveSystem(c, polyEqs, solveVars, budget);
    bool lamFirst = true;
    if (rawSols.empty() && m > 0) {
        std::vector<Expr> altVars;
        altVars.reserve(n + m);
        for (Expr xv : vars)
            altVars.push_back(xv);
        for (Expr lv : lamVars)
            altVars.push_back(lv);
        rawSols = solveSystem(c, polyEqs, altVars, budget);
        lamFirst = false;
    }

    if (rawSols.empty()) {
        out.reason = "no stationary points found";
        return out;
    }

    // Precompute symbolic Hessian of Lagrangian L(x, lam) = f(x) - sum_j lam_j * g_j(x)
    // and constraint gradients for second-order classification.
    std::vector<Expr> lagTerms{f};
    for (std::size_t j = 0; j < m; ++j)
        lagTerms.push_back(c.neg(c.mul({lamVars[j], constraints[j]})));
    const Expr lagrangian = c.add(lagTerms);
    const SymMatrix hessL = hessian(c, lagrangian, vars);
    const SymMatrix gradG0 =
        (m == 1) ? gradient(c, constraints[0], vars) : SymMatrix{};

    std::vector<Expr> allSyms;
    allSyms.reserve(n + m);
    for (Expr xv : vars)
        allSyms.push_back(xv);
    for (Expr lv : lamVars)
        allSyms.push_back(lv);

    for (const std::vector<Expr> &sol : rawSols) {
        if (sol.size() != n + m)
            continue;
        std::vector<Expr> xStar(n);
        std::vector<Expr> lamStar(m);
        if (lamFirst) {
            for (std::size_t j = 0; j < m; ++j)
                lamStar[j] = c.simplify(sol[j]);
            for (std::size_t i = 0; i < n; ++i)
                xStar[i] = c.simplify(sol[m + i]);
        } else {
            for (std::size_t i = 0; i < n; ++i)
                xStar[i] = c.simplify(sol[i]);
            for (std::size_t j = 0; j < m; ++j)
                lamStar[j] = c.simplify(sol[n + j]);
        }

        std::vector<Expr> allVals;
        allVals.reserve(n + m);
        for (Expr xv : xStar)
            allVals.push_back(xv);
        for (Expr lv : lamStar)
            allVals.push_back(lv);

        // Certify KKT stationarity and constraint equations on the original residuals.
        bool kktOk = true;
        for (const Expr &resExpr : kktResiduals) {
            const Expr subbed =
                subsSimultaneousLinalg(c, resExpr, allSyms, allVals);
            if (subbed.isNull() || !isZeroLinalg(c, subbed, budget)) {
                kktOk = false;
                break;
            }
        }
        if (!kktOk)
            continue;

        const Expr fVal =
            c.simplify(subsSimultaneousLinalg(c, f, vars, xStar));
        if (fVal.isNull())
            continue;

        ExtremumPoint pt;
        pt.point = xStar;
        pt.multipliers = lamStar;
        pt.value = fVal;
        pt.kind = ExtremumPoint::Classification::Unknown;

        // Second-order classification when Hessian entries evaluate numerically
        SymMatrix HStar(n, n, c.zero());
        for (std::size_t r = 0; r < n; ++r) {
            for (std::size_t col = 0; col < n; ++col) {
                HStar.at(r, col) = c.simplify(subsSimultaneousLinalg(
                    c, hessL.at(r, col), allSyms, allVals));
            }
        }

        if (m == 0) {
            bool allMinorsOk = true;
            bool allPos = true;
            bool altNegPos = true;
            int lastSign = 0;
            for (std::size_t k = 1; k <= n; ++k) {
                bool okM = false;
                const int s = leadingMinorSign(c, HStar, k, budget, okM);
                if (!okM || s == 0) {
                    allMinorsOk = false;
                    break;
                }
                if (s <= 0)
                    allPos = false;
                const int wantMaxSign = (k % 2 == 1) ? -1 : +1;
                if (s != wantMaxSign)
                    altNegPos = false;
                if (k == n)
                    lastSign = s;
            }
            if (allMinorsOk) {
                if (allPos)
                    pt.kind = ExtremumPoint::Classification::LocalMinimum;
                else if (altNegPos)
                    pt.kind = ExtremumPoint::Classification::LocalMaximum;
                else if (lastSign != 0)
                    pt.kind = ExtremumPoint::Classification::SaddlePoint;
            }
        } else if (m == 1 && n >= 2) {
            std::vector<Expr> gGrad(n);
            for (std::size_t i = 0; i < n; ++i) {
                gGrad[i] = c.simplify(
                    subsSimultaneousLinalg(c, gradG0.at(i, 0), vars, xStar));
            }
            std::vector<std::size_t> perm(n);
            for (std::size_t i = 0; i < n; ++i)
                perm[i] = i;
            for (std::size_t i = 0; i < n; ++i) {
                int sG = 0;
                if (evalExprSign(c, gGrad[i], sG) && sG != 0) {
                    std::swap(perm[0], perm[i]);
                    break;
                }
            }

            SymMatrix B(n + 1, n + 1, c.zero());
            for (std::size_t i = 0; i < n; ++i) {
                B.at(0, i + 1) = gGrad[perm[i]];
                B.at(i + 1, 0) = gGrad[perm[i]];
                for (std::size_t j = 0; j < n; ++j)
                    B.at(i + 1, j + 1) = HStar.at(perm[i], perm[j]);
            }

            bool allMinorsOk = true;
            bool allNeg = true;
            bool altSigns = true;
            int lastSign = 0;
            for (std::size_t k = 2; k <= n; ++k) {
                bool okB = false;
                const int s = leadingMinorSign(c, B, k + 1, budget, okB);
                if (!okB || s == 0) {
                    allMinorsOk = false;
                    break;
                }
                if (s >= 0)
                    allNeg = false;
                const int wantMaxSign = (k % 2 == 0) ? +1 : -1;
                if (s != wantMaxSign)
                    altSigns = false;
                if (k == n)
                    lastSign = s;
            }
            if (allMinorsOk) {
                if (allNeg)
                    pt.kind = ExtremumPoint::Classification::LocalMinimum;
                else if (altSigns)
                    pt.kind = ExtremumPoint::Classification::LocalMaximum;
                else if (n >= 3 && lastSign != 0)
                    pt.kind = ExtremumPoint::Classification::SaddlePoint;
            }
        }

        // Deduplicate by coordinate vector
        bool dup = false;
        for (const ExtremumPoint &prev : out.points) {
            if (prev.point == pt.point) {
                dup = true;
                break;
            }
        }
        if (!dup)
            out.points.push_back(std::move(pt));
    }

    if (out.points.empty()) {
        out.reason = "no certified KKT stationary points found";
        return out;
    }

    std::sort(out.points.begin(), out.points.end(),
              [&c](const ExtremumPoint &a, const ExtremumPoint &b) {
                  for (std::size_t i = 0; i < a.point.size(); ++i) {
                      const int cmp = c.compare(a.point[i], b.point[i]);
                      if (cmp != 0)
                          return cmp < 0;
                  }
                  return false;
              });

    out.certified = true;
    out.status = LagrangeExtremaResult::Status::ProvedSymbolic;
    return out;
}

Expr poissonBracket(Ctx &c, Expr f, Expr g, const std::vector<Expr> &q,
                    const std::vector<Expr> &p)
{
    if (f.isNull() || g.isNull() || q.empty() || q.size() != p.size())
        return Expr{};
    std::vector<Expr> terms;
    terms.reserve(2 * q.size());
    for (std::size_t i = 0; i < q.size(); ++i) {
        if (q[i].isNull() || p[i].isNull() || c.kind(q[i]) != NodeKind::Symbol ||
            c.kind(p[i]) != NodeKind::Symbol) {
            return Expr{};
        }
        const Expr dfdq = c.diff(f, q[i]);
        const Expr dgdp = c.diff(g, p[i]);
        const Expr dfdp = c.diff(f, p[i]);
        const Expr dgdq = c.diff(g, q[i]);
        terms.push_back(c.mul({dfdq, dgdp}));
        terms.push_back(c.neg(c.mul({dfdp, dgdq})));
    }
    return c.simplify(c.add(terms));
}

namespace {

Expr synthesizeNextDerivSymbol(Ctx &c, Expr qSym,
                               const std::vector<Expr> &existing,
                               std::size_t nextOrder)
{
    const std::string &qName = c.symbolName(qSym);
    if (!existing.empty() && c.kind(existing[0]) == NodeKind::Symbol) {
        const std::string &d1 = c.symbolName(existing[0]);
        if (d1 == "d" + qName) {
            return c.symbol(std::string(nextOrder, 'd') + qName);
        }
        if (d1 == qName + "dot" && nextOrder == 2) {
            return c.symbol(qName + "ddot");
        }
        if (d1 == qName + "_1") {
            return c.symbol(qName + "_" + std::to_string(nextOrder));
        }
    }
    if (nextOrder == 1)
        return c.symbol("d" + qName);
    if (nextOrder == 2)
        return c.symbol("dd" + qName);
    return c.symbol("d" + std::to_string(nextOrder) + qName);
}

Expr totalTimeDerivative(Ctx &c, Expr expr, Expr t,
                         std::vector<VariationalField> &fields)
{
    if (expr.isNull())
        return Expr{};
    std::vector<Expr> terms;
    if (!t.isNull() && c.kind(t) == NodeKind::Symbol) {
        const Expr dt = c.diff(expr, t);
        if (!c.isZero(dt))
            terms.push_back(dt);
    }
    for (VariationalField &fld : fields) {
        if (fld.q.isNull() || c.kind(fld.q) != NodeKind::Symbol)
            continue;
        if (fld.derivatives.empty()) {
            fld.derivatives.push_back(
                synthesizeNextDerivSymbol(c, fld.q, fld.derivatives, 1));
        }
        const Expr dq = c.diff(expr, fld.q);
        if (!c.isZero(dq))
            terms.push_back(c.mul({dq, fld.derivatives[0]}));

        const std::size_t curLen = fld.derivatives.size();
        for (std::size_t k = 0; k < curLen; ++k) {
            const Expr dSym = fld.derivatives[k];
            if (dSym.isNull() || c.kind(dSym) != NodeKind::Symbol)
                continue;
            const Expr ddk = c.diff(expr, dSym);
            if (c.isZero(ddk))
                continue;
            if (k + 1 >= fld.derivatives.size()) {
                fld.derivatives.push_back(synthesizeNextDerivSymbol(
                    c, fld.q, fld.derivatives, k + 2));
            }
            terms.push_back(c.mul({ddk, fld.derivatives[k + 1]}));
        }
    }
    return terms.empty() ? c.zero() : c.simplify(c.add(terms));
}

} // namespace

EulerLagrangeResult eulerLagrange(Ctx &c, Expr L, Expr t,
                                  const std::vector<VariationalField> &fields)
{
    EulerLagrangeResult out;
    if (L.isNull() || fields.empty())
        return out;

    std::vector<VariationalField> workFields = fields;
    for (const VariationalField &fld : workFields) {
        if (fld.q.isNull() || c.kind(fld.q) != NodeKind::Symbol)
            return EulerLagrangeResult{};
        for (Expr dSym : fld.derivatives) {
            if (dSym.isNull() || c.kind(dSym) != NodeKind::Symbol)
                return EulerLagrangeResult{};
        }
    }

    if (t.isNull() || c.kind(t) != NodeKind::Symbol) {
        out.autonomous = true;
    } else {
        out.autonomous = isZeroLinalg(c, c.diff(L, t), nullptr);
    }

    std::vector<Expr> energySumTerms;
    out.equations.reserve(fields.size());
    out.momenta.reserve(fields.size());

    for (std::size_t i = 0; i < fields.size(); ++i) {
        const VariationalField &origFld = fields[i];
        const Expr dLdq = c.simplify(c.diff(L, origFld.q));
        Expr p_i = c.zero();
        if (!origFld.derivatives.empty()) {
            p_i = c.simplify(c.diff(L, origFld.derivatives[0]));
            energySumTerms.push_back(c.mul({origFld.derivatives[0], p_i}));
        }
        out.momenta.push_back(p_i);

        bool dependsHigher = false;
        for (std::size_t k = 1; k < origFld.derivatives.size(); ++k) {
            if (!isZeroLinalg(c, c.diff(L, origFld.derivatives[k]), nullptr)) {
                dependsHigher = true;
                break;
            }
        }
        if (isZeroLinalg(c, dLdq, nullptr) && !dependsHigher) {
            out.cyclicCoords.push_back(origFld.q);
            out.conservedMomenta.push_back(p_i);
        }

        std::vector<Expr> elTerms{dLdq};
        for (std::size_t k = 0; k < origFld.derivatives.size(); ++k) {
            Expr term = c.simplify(c.diff(L, origFld.derivatives[k]));
            if (c.isZero(term))
                continue;
            for (std::size_t step = 0; step <= k; ++step)
                term = totalTimeDerivative(c, term, t, workFields);
            if ((k + 1) % 2 != 0)
                term = c.neg(term);
            elTerms.push_back(term);
        }
        out.equations.push_back(c.simplify(c.add(elTerms)));
    }

    energySumTerms.push_back(c.neg(L));
    out.energy = c.simplify(c.add(energySumTerms));
    return out;
}

EulerLagrangeResult eulerLagrange(Ctx &c, Expr L, Expr t,
                                  const std::vector<Expr> &q,
                                  const std::vector<Expr> &dq,
                                  const std::vector<Expr> &ddq)
{
    if (q.empty() || q.size() != dq.size() ||
        (!ddq.empty() && ddq.size() != q.size())) {
        return EulerLagrangeResult{};
    }
    std::vector<VariationalField> fields(q.size());
    for (std::size_t i = 0; i < q.size(); ++i) {
        fields[i].q = q[i];
        fields[i].derivatives.push_back(dq[i]);
        if (!ddq.empty() && !ddq[i].isNull())
            fields[i].derivatives.push_back(ddq[i]);
    }
    return eulerLagrange(c, L, t, fields);
}

HamiltonEquationsResult hamiltonEquations(Ctx &c, Expr H,
                                          const std::vector<Expr> &q,
                                          const std::vector<Expr> &p)
{
    HamiltonEquationsResult out;
    if (H.isNull() || q.empty() || q.size() != p.size()) {
        out.reason = "invalid Hamiltonian or phase-space variables";
        return out;
    }
    for (std::size_t i = 0; i < q.size(); ++i) {
        if (q[i].isNull() || p[i].isNull() || c.kind(q[i]) != NodeKind::Symbol ||
            c.kind(p[i]) != NodeKind::Symbol) {
            out.reason = "phase-space coordinates and momenta must be symbols";
            return out;
        }
    }

    out.H = c.simplify(H);
    out.dqdt.resize(q.size());
    out.dpdt.resize(p.size());
    bool allCert = true;
    for (std::size_t i = 0; i < q.size(); ++i) {
        out.dqdt[i] = c.simplify(c.diff(out.H, p[i]));
        out.dpdt[i] = c.simplify(c.neg(c.diff(out.H, q[i])));
        const Expr pbQ = poissonBracket(c, q[i], out.H, q, p);
        const Expr pbP = poissonBracket(c, p[i], out.H, q, p);
        if (!isZeroLinalg(c, c.add({out.dqdt[i], c.neg(pbQ)}), nullptr) ||
            !isZeroLinalg(c, c.add({out.dpdt[i], c.neg(pbP)}), nullptr)) {
            allCert = false;
        }
    }
    const Expr pbHH = poissonBracket(c, out.H, out.H, q, p);
    if (!isZeroLinalg(c, pbHH, nullptr))
        allCert = false;
    out.certified = allCert;
    return out;
}

HamiltonEquationsResult legendreTransform(Ctx &c, Expr L,
                                          const std::vector<Expr> &q,
                                          const std::vector<Expr> &dq,
                                          const std::vector<Expr> &p,
                                          Budget *budget)
{
    HamiltonEquationsResult out;
    const std::size_t n = q.size();
    if (L.isNull() || n == 0 || dq.size() != n || p.size() != n) {
        out.reason =
            "legendreTransform requires non-empty matching q, dq, and p vectors";
        return out;
    }
    for (std::size_t i = 0; i < n; ++i) {
        if (q[i].isNull() || dq[i].isNull() || p[i].isNull() ||
            c.kind(q[i]) != NodeKind::Symbol ||
            c.kind(dq[i]) != NodeKind::Symbol ||
            c.kind(p[i]) != NodeKind::Symbol) {
            out.reason = "q, dq, and p entries must be symbols";
            return out;
        }
    }

    std::vector<Expr> pOfDq(n);
    for (std::size_t i = 0; i < n; ++i)
        pOfDq[i] = c.simplify(c.diff(L, dq[i]));

    // 1. Fast path: affine momentum map P(q, dq) = M(q) * dq + b(q)
    //    (covers all natural and gyroscopic mechanical systems quadratic in dq).
    SymMatrix M = jacobian(c, pOfDq, dq);
    bool isAffineInDq = true;
    for (std::size_t i = 0; i < n && isAffineInDq; ++i) {
        for (std::size_t j = 0; j < n; ++j) {
            for (std::size_t k = 0; k < n; ++k) {
                if (!isZeroLinalg(c, c.diff(M.at(i, j), dq[k]), budget)) {
                    isAffineInDq = false;
                    break;
                }
            }
        }
    }

    std::vector<Expr> dqSol;
    if (isAffineInDq) {
        std::vector<Expr> zeroDq(n, c.zero());
        SymMatrix rhs(n, 1, c.zero());
        for (std::size_t i = 0; i < n; ++i) {
            const Expr b_i = subsSimultaneousLinalg(c, pOfDq[i], dq, zeroDq);
            rhs.at(i, 0) = c.simplify(c.add({p[i], c.neg(b_i)}));
        }
        const SymMatrix solMat = linsolve(c, M, rhs, budget);
        if (solMat.rows() == n && solMat.cols() == 1) {
            dqSol.resize(n);
            for (std::size_t i = 0; i < n; ++i)
                dqSol[i] = c.simplify(solMat.at(i, 0));
        }
    }

    // 2. Fallback: nonlinear algebraic system solveSystem(P_i(q, dq) - p_i == 0, dq).
    if (dqSol.empty()) {
        std::vector<Expr> eqs(n);
        for (std::size_t i = 0; i < n; ++i)
            eqs[i] = c.add({pOfDq[i], c.neg(p[i])});
        const std::vector< std::vector<Expr> > sols =
            solveSystem(c, eqs, dq, budget);
        if (!sols.empty() && sols[0].size() == n)
            dqSol = sols[0];
    }

    if (dqSol.size() != n) {
        out.reason =
            "failed to invert canonical momentum map p_i = dL/d(dq_i)";
        return out;
    }

    std::vector<Expr> hTerms;
    hTerms.reserve(n + 1);
    for (std::size_t i = 0; i < n; ++i)
        hTerms.push_back(c.mul({p[i], dqSol[i]}));
    const Expr lSub = subsSimultaneousLinalg(c, L, dq, dqSol);
    hTerms.push_back(c.neg(lSub));
    const Expr H = c.simplify(c.add(hTerms));

    out = hamiltonEquations(c, H, q, p);
    out.qDotFromP = dqSol;

    // Certify Legendre involution: dH/dp_i == dqSol[i].
    for (std::size_t i = 0; i < n; ++i) {
        if (!isZeroLinalg(c, c.add({out.dqdt[i], c.neg(dqSol[i])}), budget)) {
            out.certified = false;
            out.reason = "Legendre involution certificate dH/dp_i == dq_i(q, p) failed";
            break;
        }
    }
    return out;
}

// ---------------------------------------------------------------------------
// Differential Geometry of Curves/Surfaces & Riemannian Geometry (Item 76)
// ---------------------------------------------------------------------------

namespace {

Expr dot3Linalg(Ctx &c, const std::vector<Expr> &a, const std::vector<Expr> &b)
{
    return c.simplify(c.add({c.mul({a[0], b[0]}),
                             c.mul({a[1], b[1]}),
                             c.mul({a[2], b[2]})}));
}

std::vector<Expr> cross3Linalg(Ctx &c, const std::vector<Expr> &a,
                               const std::vector<Expr> &b)
{
    return {
        c.simplify(c.add({c.mul({a[1], b[2]}), c.neg(c.mul({a[2], b[1]}))})),
        c.simplify(c.add({c.mul({a[2], b[0]}), c.neg(c.mul({a[0], b[2]}))})),
        c.simplify(c.add({c.mul({a[0], b[1]}), c.neg(c.mul({a[1], b[0]}))}))
    };
}

Expr positiveSqrtLinalg(Ctx &c, Expr sqExpr, const std::vector<Expr> &vars)
{
    Expr s = c.simplify(sqExpr);
    if (c.isZero(s) || s == c.one())
        return s;

    for (const Expr &v : vars) {
        if (!v.isNull() && c.kind(v) == NodeKind::Symbol) {
            Expr f;
            if (factorExpr(c, s, v, f) && !f.isNull() &&
                (c.kind(f) == NodeKind::Pow || c.kind(f) == NodeKind::Mul)) {
                s = f;
                break;
            }
        }
    }

    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
    auto sqrtFactor = [&](Expr f) -> Expr {
        if (c.kind(f) == NodeKind::Pow &&
            c.kind(c.child(f, 1)) == NodeKind::Number) {
            const Rational &re = c.numberValue(c.child(f, 1));
            std::int64_t expInt = 0;
            if (re.den() == BigInt(1) && re.num().fitsInt64(expInt) &&
                expInt % 2 == 0) {
                Expr base = c.child(f, 0);
                // Ensure canonical positive orientation for polynomial sum bases
                double dProbe = 0.0;
                std::vector<std::pair<std::string, double>> env;
                for (const Expr &v : vars) {
                    if (!v.isNull() && c.kind(v) == NodeKind::Symbol)
                        env.emplace_back(std::string(c.symbolName(v)), 0.7);
                }
                if (((expInt / 2) % 2 != 0) && c.evalDouble(base, env, dProbe) &&
                    dProbe < 0.0) {
                    base = c.neg(base);
                }
                return c.pow(base, c.number(expInt / 2));
            }
        }
        return c.pow(f, half);
    };

    if (c.kind(s) == NodeKind::Mul) {
        std::vector<Expr> parts;
        for (std::size_t i = 0; i < c.childCount(s); ++i)
            parts.push_back(sqrtFactor(c.child(s, i)));
        return c.simplify(c.mul(parts));
    }
    return c.simplify(sqrtFactor(s));
}

} // namespace

FrenetSerretResult frenetSerret(Ctx &c, const std::vector<Expr> &curve,
                                Expr t, Budget *budget)
{
    FrenetSerretResult out;
    if ((curve.size() != 2 && curve.size() != 3) || t.isNull() ||
        c.kind(t) != NodeKind::Symbol) {
        out.reason = "frenetSerret requires a 2D or 3D curve and parameter symbol t";
        return out;
    }
    if (!checkLinalgBudget(c, budget)) {
        out.reason = "budget exhausted";
        return out;
    }

    std::vector<Expr> r(3, c.zero());
    for (std::size_t i = 0; i < curve.size(); ++i) {
        if (curve[i].isNull()) {
            out.reason = "null curve component";
            return out;
        }
        r[i] = curve[i];
    }

    std::vector<Expr> r1(3), r2(3), r3(3);
    for (int i = 0; i < 3; ++i) {
        r1[i] = c.simplify(c.diff(r[i], t));
        r2[i] = c.simplify(c.diff(r1[i], t));
        r3[i] = c.simplify(c.diff(r2[i], t));
    }

    const Expr speedSq = dot3Linalg(c, r1, r1);
    if (isZeroLinalg(c, speedSq, budget)) {
        out.reason = "singular curve (r'(t) == 0)";
        return out;
    }
    out.speed = positiveSqrtLinalg(c, speedSq, {t});

    out.T.resize(3);
    for (int i = 0; i < 3; ++i)
        out.T[i] = normLinalg(c, c.div(r1[i], out.speed), budget);

    const std::vector<Expr> cross12 = cross3Linalg(c, r1, r2);
    const Expr crossNormSq = dot3Linalg(c, cross12, cross12);
    if (isZeroLinalg(c, crossNormSq, budget)) {
        // Straight line (zero curvature): T is well-defined, kappa = 0, tau = 0
        out.curvature = c.zero();
        out.torsion = c.zero();
        out.N = {c.zero(), c.zero(), c.zero()};
        out.B = {c.zero(), c.zero(), c.zero()};
        out.certified = isZeroLinalg(
            c, c.add({dot3Linalg(c, out.T, out.T), c.neg(c.one())}), budget);
        return out;
    }

    const Expr crossNorm = positiveSqrtLinalg(c, crossNormSq, {t});
    out.B.resize(3);
    for (int i = 0; i < 3; ++i)
        out.B[i] = normLinalg(c, c.div(cross12[i], crossNorm), budget);

    const std::vector<Expr> nVec = cross3Linalg(c, out.B, out.T);
    out.N.resize(3);
    for (int i = 0; i < 3; ++i)
        out.N[i] = normLinalg(c, nVec[i], budget);

    const Expr speedCubed = c.mul({speedSq, out.speed});
    out.curvature = normLinalg(c, c.div(crossNorm, speedCubed), budget);

    const Expr tripleProd = dot3Linalg(c, cross12, r3);
    out.torsion = normLinalg(c, c.div(tripleProd, crossNormSq), budget);

    // Certify orthonormality: T.T == 1, N.N == 1, B.B == 1, T.N == 0, T.B == 0, N.B == 0
    const bool orthoOk =
        isZeroLinalg(c, c.add({dot3Linalg(c, out.T, out.T), c.neg(c.one())}), budget) &&
        isZeroLinalg(c, c.add({dot3Linalg(c, out.N, out.N), c.neg(c.one())}), budget) &&
        isZeroLinalg(c, c.add({dot3Linalg(c, out.B, out.B), c.neg(c.one())}), budget) &&
        isZeroLinalg(c, dot3Linalg(c, out.T, out.N), budget) &&
        isZeroLinalg(c, dot3Linalg(c, out.T, out.B), budget) &&
        isZeroLinalg(c, dot3Linalg(c, out.N, out.B), budget);

    out.certified = orthoOk;
    if (!orthoOk)
        out.reason = "Frenet-Serret frame failed orthonormality certificate";
    return out;
}

SurfaceCurvatureResult surfaceCurvature(Ctx &c,
                                        const std::vector<Expr> &surface,
                                        Expr u, Expr v,
                                        Budget *budget)
{
    SurfaceCurvatureResult out;
    if (surface.size() != 3 || u.isNull() || v.isNull() ||
        c.kind(u) != NodeKind::Symbol || c.kind(v) != NodeKind::Symbol) {
        out.reason = "surfaceCurvature requires a 3D surface r(u, v) and parameter symbols u, v";
        return out;
    }
    if (!checkLinalgBudget(c, budget)) {
        out.reason = "budget exhausted";
        return out;
    }

    std::vector<Expr> ru(3), rv(3), ruu(3), ruv(3), rvv(3);
    for (int i = 0; i < 3; ++i) {
        if (surface[i].isNull()) {
            out.reason = "null surface component";
            return out;
        }
        ru[i] = c.simplify(c.diff(surface[i], u));
        rv[i] = c.simplify(c.diff(surface[i], v));
        ruu[i] = c.simplify(c.diff(ru[i], u));
        ruv[i] = c.simplify(c.diff(ru[i], v));
        rvv[i] = c.simplify(c.diff(rv[i], v));
    }

    out.E = normLinalg(c, dot3Linalg(c, ru, ru), budget);
    out.F = normLinalg(c, dot3Linalg(c, ru, rv), budget);
    out.G = normLinalg(c, dot3Linalg(c, rv, rv), budget);
    out.firstForm = SymMatrix(2, 2, {out.E, out.F, out.F, out.G});

    const std::vector<Expr> crossUV = cross3Linalg(c, ru, rv);
    const Expr detI = normLinalg(
        c, c.add({c.mul({out.E, out.G}), c.neg(c.mul({out.F, out.F}))}), budget);
    if (isZeroLinalg(c, detI, budget)) {
        out.reason = "degenerate surface patch (E*G - F^2 == 0)";
        return out;
    }
    out.areaElement = positiveSqrtLinalg(c, detI, {u, v});

    out.normal.resize(3);
    for (int i = 0; i < 3; ++i)
        out.normal[i] = normLinalg(c, c.div(crossUV[i], out.areaElement), budget);

    out.L = normLinalg(c, dot3Linalg(c, ruu, out.normal), budget);
    out.M = normLinalg(c, dot3Linalg(c, ruv, out.normal), budget);
    out.N = normLinalg(c, dot3Linalg(c, rvv, out.normal), budget);
    out.secondForm = SymMatrix(2, 2, {out.L, out.M, out.M, out.N});

    const SymMatrix invI = inv(c, out.firstForm, budget);
    if (invI.empty()) {
        out.reason = "first fundamental form is singular";
        return out;
    }
    out.shapeOperator = invI.mul(c, out.secondForm);
    for (std::size_t r = 0; r < 2; ++r)
        for (std::size_t col = 0; col < 2; ++col)
            out.shapeOperator.at(r, col) =
                normLinalg(c, out.shapeOperator.at(r, col), budget);

    const Expr detII = c.add({c.mul({out.L, out.N}), c.neg(c.mul({out.M, out.M}))});
    out.gaussianCurvature = normLinalg(c, c.div(detII, detI), budget);

    const Expr two = c.number(std::int64_t{2});
    const Expr numH = c.add({c.mul({out.E, out.N}),
                             c.neg(c.mul({two, out.F, out.M})),
                             c.mul({out.G, out.L})});
    out.meanCurvature =
        normLinalg(c, c.div(numH, c.mul({two, detI})), budget);

    // Certify: normal is orthogonal to ru and rv, and K == det(S), 2*H == tr(S)
    const Expr detS = det(c, out.shapeOperator, budget);
    const Expr trS = out.shapeOperator.trace(c);
    const bool certOk =
        isZeroLinalg(c, dot3Linalg(c, out.normal, ru), budget) &&
        isZeroLinalg(c, dot3Linalg(c, out.normal, rv), budget) &&
        isZeroLinalg(c, c.add({out.gaussianCurvature, c.neg(detS)}), budget) &&
        isZeroLinalg(c, c.add({c.mul({two, out.meanCurvature}), c.neg(trS)}),
                     budget);

    out.certified = certOk;
    if (!certOk)
        out.reason = "surfaceCurvature failed normal orthogonality or Weingarten certificate";
    return out;
}

ChristoffelResult christoffelSymbols(Ctx &c, const SymMatrix &metric,
                                     const std::vector<Expr> &coords,
                                     Budget *budget)
{
    ChristoffelResult out;
    const std::size_t n = coords.size();
    if (!metric.isSquare() || metric.rows() != n || n == 0) {
        out.reason = "christoffelSymbols requires an n x n metric and n coordinate symbols";
        return out;
    }
    for (std::size_t i = 0; i < n; ++i) {
        if (coords[i].isNull() || c.kind(coords[i]) != NodeKind::Symbol) {
            out.reason = "coordinate entries must be symbols";
            return out;
        }
    }
    if (!checkLinalgBudget(c, budget)) {
        out.reason = "budget exhausted";
        return out;
    }

    out.metric = metric;
    out.inverseMetric = inv(c, metric, budget);
    if (out.inverseMetric.empty()) {
        out.reason = "metric tensor is singular";
        return out;
    }
    for (std::size_t i = 0; i < n; ++i)
        for (std::size_t j = 0; j < n; ++j)
            out.inverseMetric.at(i, j) =
                normLinalg(c, out.inverseMetric.at(i, j), budget);

    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
    out.firstKind.assign(n, SymMatrix::zeros(c, n, n));
    out.secondKind.assign(n, SymMatrix::zeros(c, n, n));

    for (std::size_t k = 0; k < n; ++k) {
        for (std::size_t i = 0; i < n; ++i) {
            for (std::size_t j = i; j < n; ++j) {
                const Expr di_gkj = c.diff(metric.at(k, j), coords[i]);
                const Expr dj_gki = c.diff(metric.at(k, i), coords[j]);
                const Expr dk_gij = c.diff(metric.at(i, j), coords[k]);
                const Expr gamma1 = normLinalg(
                    c, c.mul({half, c.add({di_gkj, dj_gki, c.neg(dk_gij)})}),
                    budget);
                out.firstKind[k].at(i, j) = gamma1;
                out.firstKind[k].at(j, i) = gamma1;
            }
        }
    }

    for (std::size_t k = 0; k < n; ++k) {
        for (std::size_t i = 0; i < n; ++i) {
            for (std::size_t j = i; j < n; ++j) {
                std::vector<Expr> sumTerms;
                for (std::size_t m = 0; m < n; ++m) {
                    const Expr gkm = out.inverseMetric.at(k, m);
                    const Expr gmij = out.firstKind[m].at(i, j);
                    if (!c.isZero(gkm) && !c.isZero(gmij))
                        sumTerms.push_back(c.mul({gkm, gmij}));
                }
                const Expr gamma2 =
                    sumTerms.empty() ? c.zero()
                                     : normLinalg(c, c.add(sumTerms), budget);
                out.secondKind[k].at(i, j) = gamma2;
                out.secondKind[k].at(j, i) = gamma2;
            }
        }
    }

    // Certify metric compatibility: nabla_k g_{ij} = d_k g_{ij} - g_{mj} Gamma^m_{ki} - g_{im} Gamma^m_{kj} == 0
    bool compatOk = true;
    for (std::size_t k = 0; k < n && compatOk; ++k) {
        for (std::size_t i = 0; i < n && compatOk; ++i) {
            for (std::size_t j = i; j < n && compatOk; ++j) {
                std::vector<Expr> terms{c.diff(metric.at(i, j), coords[k])};
                for (std::size_t m = 0; m < n; ++m) {
                    terms.push_back(c.neg(
                        c.mul({metric.at(m, j), out.secondKind[m].at(k, i)})));
                    terms.push_back(c.neg(
                        c.mul({metric.at(i, m), out.secondKind[m].at(k, j)})));
                }
                if (!isZeroLinalg(c, c.add(terms), budget))
                    compatOk = false;
            }
        }
    }

    out.certified = compatOk;
    if (!compatOk)
        out.reason = "Christoffel symbols failed metric-compatibility certificate nabla_k g_{ij} == 0";
    return out;
}

RiemannCurvatureResult riemannTensor(Ctx &c, const SymMatrix &metric,
                                     const std::vector<Expr> &coords,
                                     Budget *budget)
{
    RiemannCurvatureResult out;
    out.christoffel = christoffelSymbols(c, metric, coords, budget);
    if (!out.christoffel.certified) {
        out.reason = out.christoffel.reason;
        return out;
    }

    const std::size_t n = coords.size();
    const auto &G = out.christoffel.secondKind;
    out.riemann.assign(n, std::vector<SymMatrix>(n, SymMatrix::zeros(c, n, n)));

    for (std::size_t rho = 0; rho < n; ++rho) {
        for (std::size_t sigma = 0; sigma < n; ++sigma) {
            for (std::size_t mu = 0; mu < n; ++mu) {
                for (std::size_t nu = mu + 1; nu < n; ++nu) {
                    std::vector<Expr> terms{
                        c.diff(G[rho].at(nu, sigma), coords[mu]),
                        c.neg(c.diff(G[rho].at(mu, sigma), coords[nu]))};
                    for (std::size_t lam = 0; lam < n; ++lam) {
                        terms.push_back(
                            c.mul({G[rho].at(mu, lam), G[lam].at(nu, sigma)}));
                        terms.push_back(c.neg(
                            c.mul({G[rho].at(nu, lam), G[lam].at(mu, sigma)})));
                    }
                    const Expr val = normLinalg(c, c.add(terms), budget);
                    out.riemann[rho][sigma].at(mu, nu) = val;
                    out.riemann[rho][sigma].at(nu, mu) =
                        normLinalg(c, c.neg(val), budget);
                }
            }
        }
    }

    // Ricci tensor: R_{sigma, nu} = sum_rho R^rho_{sigma, rho, nu}
    out.ricci = SymMatrix::zeros(c, n, n);
    for (std::size_t sigma = 0; sigma < n; ++sigma) {
        for (std::size_t nu = 0; nu < n; ++nu) {
            std::vector<Expr> terms;
            for (std::size_t rho = 0; rho < n; ++rho) {
                const Expr rVal = out.riemann[rho][sigma].at(rho, nu);
                if (!c.isZero(rVal))
                    terms.push_back(rVal);
            }
            out.ricci.at(sigma, nu) =
                terms.empty() ? c.zero() : normLinalg(c, c.add(terms), budget);
        }
    }

    // Scalar curvature: R = sum_{sigma, nu} g^{sigma, nu} R_{sigma, nu}
    std::vector<Expr> scalarTerms;
    for (std::size_t sigma = 0; sigma < n; ++sigma) {
        for (std::size_t nu = 0; nu < n; ++nu) {
            const Expr gInv = out.christoffel.inverseMetric.at(sigma, nu);
            const Expr ric = out.ricci.at(sigma, nu);
            if (!c.isZero(gInv) && !c.isZero(ric))
                scalarTerms.push_back(c.mul({gInv, ric}));
        }
    }
    out.scalarCurvature = scalarTerms.empty()
                              ? c.zero()
                              : normLinalg(c, c.add(scalarTerms), budget);

    // Einstein tensor: G_{mu, nu} = R_{mu, nu} - 1/2 * R * g_{mu, nu}
    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
    out.einstein = SymMatrix::zeros(c, n, n);
    for (std::size_t mu = 0; mu < n; ++mu) {
        for (std::size_t nu = 0; nu < n; ++nu) {
            out.einstein.at(mu, nu) = normLinalg(
                c, c.add({out.ricci.at(mu, nu),
                          c.neg(c.mul({half, out.scalarCurvature,
                                       metric.at(mu, nu)}))}),
                budget);
        }
    }

    // Certify first algebraic Bianchi identity:
    //   R^rho_{sigma, mu, nu} + R^rho_{mu, nu, sigma} + R^rho_{nu, sigma, mu} == 0
    bool bianchiOk = true;
    for (std::size_t rho = 0; rho < n && bianchiOk; ++rho) {
        for (std::size_t s = 0; s < n && bianchiOk; ++s) {
            for (std::size_t mu = 0; mu < n && bianchiOk; ++mu) {
                for (std::size_t nu = 0; nu < n && bianchiOk; ++nu) {
                    const Expr cyc = c.add({out.riemann[rho][s].at(mu, nu),
                                            out.riemann[rho][mu].at(nu, s),
                                            out.riemann[rho][nu].at(s, mu)});
                    if (!isZeroLinalg(c, cyc, budget))
                        bianchiOk = false;
                }
            }
        }
    }

    out.certified = bianchiOk;
    if (!bianchiOk)
        out.reason = "Riemann tensor failed first algebraic Bianchi identity certificate";
    return out;
}

SymMatrix ricciTensor(Ctx &c, const SymMatrix &metric,
                      const std::vector<Expr> &coords,
                      Budget *budget)
{
    return riemannTensor(c, metric, coords, budget).ricci;
}

Expr scalarCurvature(Ctx &c, const SymMatrix &metric,
                     const std::vector<Expr> &coords,
                     Budget *budget)
{
    return riemannTensor(c, metric, coords, budget).scalarCurvature;
}

GeodesicResult geodesicEquations(Ctx &c, const SymMatrix &metric,
                                 const std::vector<Expr> &coords,
                                 const std::vector<Expr> &velocities,
                                 const std::vector<Expr> &accelerations,
                                 Budget *budget)
{
    GeodesicResult out;
    const ChristoffelResult ch = christoffelSymbols(c, metric, coords, budget);
    if (!ch.certified) {
        out.reason = ch.reason;
        return out;
    }

    const std::size_t n = coords.size();
    std::vector<Expr> vel(n), acc(n);
    for (std::size_t i = 0; i < n; ++i) {
        vel[i] = (i < velocities.size() && !velocities[i].isNull())
                     ? velocities[i]
                     : c.symbol("d" + std::string(c.symbolName(coords[i])));
        acc[i] = (i < accelerations.size() && !accelerations[i].isNull())
                     ? accelerations[i]
                     : c.symbol("dd" + std::string(c.symbolName(coords[i])));
    }

    out.equations.resize(n);
    out.rhs.resize(n);
    for (std::size_t k = 0; k < n; ++k) {
        std::vector<Expr> quadTerms;
        for (std::size_t i = 0; i < n; ++i) {
            for (std::size_t j = 0; j < n; ++j) {
                const Expr gkij = ch.secondKind[k].at(i, j);
                if (!c.isZero(gkij))
                    quadTerms.push_back(c.mul({gkij, vel[i], vel[j]}));
            }
        }
        const Expr gammaQuad =
            quadTerms.empty() ? c.zero() : normLinalg(c, c.add(quadTerms), budget);
        out.rhs[k] = normLinalg(c, c.neg(gammaQuad), budget);
        out.equations[k] = normLinalg(c, c.add({acc[k], gammaQuad}), budget);
    }

    // Certify equivalence with Euler-Lagrange equations of L = 1/2 * g_{ij} * vel^i * vel^j
    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
    std::vector<Expr> lTerms;
    for (std::size_t i = 0; i < n; ++i)
        for (std::size_t j = 0; j < n; ++j)
            if (!c.isZero(metric.at(i, j)))
                lTerms.push_back(c.mul({half, metric.at(i, j), vel[i], vel[j]}));
    const Expr L = lTerms.empty() ? c.zero() : c.add(lTerms);
    const EulerLagrangeResult el =
        eulerLagrange(c, L, Expr{}, coords, vel, acc);

    bool elOk = (el.equations.size() == n);
    for (std::size_t k = 0; k < n && elOk; ++k) {
        // Raised Euler-Lagrange equation: -g^{km} E_m(L) == d2x^k + Gamma^k_{ij} dx^i dx^j
        std::vector<Expr> raisedTerms;
        for (std::size_t m = 0; m < n; ++m) {
            const Expr gkm = ch.inverseMetric.at(k, m);
            if (!c.isZero(gkm) && !c.isZero(el.equations[m]))
                raisedTerms.push_back(c.neg(c.mul({gkm, el.equations[m]})));
        }
        const Expr raised =
            raisedTerms.empty() ? c.zero() : c.add(raisedTerms);
        if (!isZeroLinalg(c, c.add({out.equations[k], c.neg(raised)}), budget))
            elOk = false;
    }

    out.certified = elOk;
    if (!elOk)
        out.reason = "Geodesic equations failed Euler-Lagrange equivalence certificate";
    return out;
}

} // namespace numkit::cas
