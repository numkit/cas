#include <numkit/cas/integrate/ratint.hpp>

#include <numkit/cas/poly/modcpoly.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

#include <cassert>
#include <vector>

namespace numkit::cas {

namespace {

constexpr std::int64_t kMaxPowExp = 64;      // |k| bound in Pow extraction
constexpr std::size_t kRootSearchBits = 40;  // rational-root divisor budget

const Rational R0()
{
    return Rational(std::int64_t{0});
}
const Rational R1()
{
    return Rational(std::int64_t{1});
}

// sqrt(d) as an Expr: rational when d is a rational square, else the
// symbolic Pow(d, 1/2).
Expr sqrtExpr(Ctx &c, const Rational &d)
{
    // Rationalized form sqrt(n/q) = sqrt(n*q)/q keeps the printed
    // coefficient canonical (sqrt(1/2) -> 2^(1/2)/2).
    const BigInt nq = d.num() * d.den();
    BigInt root;
    if (nq.sqrtExact(root))
        return c.number(Rational(root, d.den()));
    return c.mul({c.number(Rational(BigInt(1), d.den())),
                  c.pow(c.number(Rational(nq, BigInt(1))), c.number(Rational(std::int64_t{1}, BigInt(2))))});
}

UPoly pmod(const UPoly &a, const UPoly &b)
{
    UPoly q, r;
    UPoly::divMod(a, b, q, r);
    return r;
}

// Partial fractions over pairwise-coprime moduli: N/(P1*..*Pk) =
// sum Bi/Pi with deg Bi < deg Pi.
std::vector<UPoly> partialFractions(const UPoly &N,
                                    const std::vector<UPoly> &Ps)
{
    std::vector<UPoly> Bs;
    UPoly rem = N;
    for (std::size_t idx = 0; idx < Ps.size(); ++idx) {
        if (idx + 1 == Ps.size()) {
            Bs.push_back(rem); // already reduced modulo the last factor
            break;
        }
        UPoly prod(R1());
        for (std::size_t j = idx + 1; j < Ps.size(); ++j)
            prod = prod * Ps[j];
        const UPoly inv = UPoly::invMod(prod % Ps[idx], Ps[idx]);
        const UPoly bi = pmod(rem * inv, Ps[idx]);
        Bs.push_back(bi);
        UPoly q, r;
        UPoly::divMod(rem - bi * prod, Ps[idx], q, r);
        assert(r.isZero());
        rem = q;
    }
    return Bs;
}

void fracAdd(UPoly &n1, UPoly &d1, const UPoly &n2, const UPoly &d2)
{
    n1 = n1 * d2 + n2 * d1;
    d1 = d1 * d2;
    const UPoly g = UPoly::gcd(n1, d1);
    if (!g.isConst()) {
        UPoly q, r;
        UPoly::divMod(n1, g, q, r);
        n1 = q;
        UPoly::divMod(d1, g, q, r);
        d1 = q;
    }
}

UPoly polyIntegral(const UPoly &p)
{
    std::vector<Rational> cs{R0()};
    for (std::size_t i = 0; i < p.coeffs().size(); ++i)
        cs.push_back(p.coeff(i) / Rational(static_cast<std::int64_t>(i + 1)));
    return UPoly(std::move(cs));
}

// All divisors of |n| by trial division; false if |n| exceeds the
// search budget (bit length).
bool smallDivisors(const BigInt &n, std::vector<BigInt> &out)
{
    out.assign(1, BigInt(1));
    BigInt m = n.abs();
    if (m.bitLength() > kRootSearchBits)
        return false;
    for (BigInt p(2); p * p <= m; p = p + BigInt(1)) {
        int e = 0;
        while (true) {
            BigInt q, r;
            BigInt::divMod(m, p, q, r);
            if (r.isZero()) {
                m = q;
                ++e;
            } else {
                break;
            }
        }
        if (e == 0)
            continue;
        const std::size_t base = out.size();
        BigInt pk(1);
        for (int i = 0; i < e; ++i) {
            pk = pk * p;
            for (std::size_t j = 0; j < base; ++j)
                out.push_back(out[j] * pk);
        }
    }
    if (!(m == BigInt(1))) {
        const std::size_t base = out.size();
        for (std::size_t j = 0; j < base; ++j)
            out.push_back(out[j] * m);
    }
    return true;
}

// One rational root of F (rational root theorem over the cleared
// integer coefficient version). False = none found or budget exceeded
// (ok = "definitely none" only when ok).
bool findOneRationalRoot(const UPoly &F, Rational &root, bool &ok)
{
    ok = true;
    if (F.isConst())
        return false;
    // Clear denominators.
    BigInt L(1);
    for (const Rational &c : F.coeffs())
        L = BigInt::lcm(L, c.den());
    std::vector<BigInt> ic;
    for (const Rational &c : F.coeffs()) {
        BigInt q, r;
        BigInt::divMod(L, c.den(), q, r);
        ic.push_back(c.num() * q);
    }
    std::vector<BigInt> ps, qs;
    if (!smallDivisors(ic.front() .isZero() ? BigInt(1) : ic.front().abs(), ps))
        return ok = false, false;
    if (!smallDivisors(ic.back().abs(), qs))
        return ok = false, false;
    for (const BigInt &p : ps) {
        for (const BigInt &q : qs) {
            for (int sign = 0; sign < 2; ++sign) {
                const Rational cand(sign == 0 ? p : -p, q);
                if (F.eval(cand).isZero()) {
                    root = cand;
                    return true;
                }
            }
        }
    }
    return false;
}

// One piece of the transcendental part with its exact derivative:
//   Log:  coeff * log(v)          -> coeff * v'/v
//   Atan: coeff * atan(v/s)       -> coeff*s*v'/(v^2 + s^2)
struct Piece
{
    enum Kind { Log, Atan } kind;
    Rational coeff;
    UPoly v;        // Log argument / Atan numerator (linear)
    Rational scale; // Atan only: s
};

// Splitting fallback: integrate A/F (F squarefree, denominator already
// reduced to the leftover factors) over rational roots and at most one
// monic quadratic; false with a reason outside that scope.
bool integrateSplitting(const UPoly &A, const UPoly &F,
                        std::vector<Piece> &pieces, std::string &reason)
{
    // Strip rational roots one by one.
    std::vector<Rational> roots;
    UPoly rest = F;
    while (!rest.isConst()) {
        Rational rt;
        bool ok = false;
        if (rest.coeff(0).isZero()) {
            rt = R0();
            ok = true;
        } else if (!findOneRationalRoot(rest, rt, ok)) {
            if (!ok) {
                reason = "rational root search budget exceeded";
                return false;
            }
            break;
        }
        roots.push_back(rt);
        UPoly q, r;
        UPoly::divMod(rest, UPoly(std::vector<Rational>{Rational(-rt), R1()}), q, r);
        assert(r.isZero());
        rest = q;
    }

    std::vector<UPoly> mods;
    for (const Rational &rt : roots)
        mods.push_back(UPoly(std::vector<Rational>{Rational(-rt), R1()}));
    if (!rest.isConst())
        mods.push_back(rest);
    if (mods.empty())
        return true; // A must be zero here (deg A < 0); nothing to do

    const std::vector<UPoly> parts = partialFractions(A, mods);
    for (std::size_t i = 0; i < roots.size(); ++i) {
        if (parts[i].isZero())
            continue;
        Piece p;
        p.kind = Piece::Log;
        p.coeff = parts[i].coeff(0);
        p.v = UPoly(std::vector<Rational>{Rational(-roots[i]), R1()});
        p.scale = R1();
        pieces.push_back(p);
    }

    if (rest.isConst())
        return true;
    if (rest.deg() > 2) {
        reason = "irreducible factor of degree > 2 (needs algebraic residues)";
        return false;
    }

    // Monic quadratic x^2 + b x + c with 4c - b^2 = s^2 > 0.
    const Rational b = rest.coeff(1);
    const Rational c0 = rest.coeff(0);
    const Rational disc = Rational(std::int64_t{4}) * c0 - b * b;
    if (disc.signum() <= 0) {
        reason = "quadratic factor with non-positive 4c-b^2";
        return false;
    }
    BigInt sn, sd;
    if (!disc.num().sqrtExact(sn) || !disc.den().sqrtExact(sd)) {
        reason = "quadratic factor with non-square 4c-b^2 "
                 "(needs algebraic extension)";
        return false;
    }
    const Rational s(sn, sd);

    const UPoly &P = parts.back(); // (p x + q)/rest
    const Rational p1 = P.coeff(1), q0 = P.coeff(0);

    Piece lp;
    lp.kind = Piece::Log;
    lp.coeff = p1 * Rational(std::int64_t{1}, BigInt(2));
    lp.v = rest;
    lp.scale = R1();
    if (!lp.coeff.isZero())
        pieces.push_back(lp);

    const Rational aCoef = (Rational(std::int64_t{2}) * q0 - p1 * b) / s;
    if (!aCoef.isZero()) {
        Piece ap;
        ap.kind = Piece::Atan;
        ap.coeff = aCoef;
        ap.v = UPoly(std::vector<Rational>{b, Rational(std::int64_t{2})}); // 2x + b
        ap.scale = s;
        pieces.push_back(ap);
    }
    return true;
}

// Integrate A/F (F squarefree): Trager's rational residues first — the
// residues are the rational roots of res(A - t*F', F), and each residue
// r contributes ONE grouped logarithm r*log(gcd(A - r*F', F)) covering
// all poles with that residue. Whatever is left falls through to the
// per-root/quadratic splitting path.
bool integrateSquarefree(Ctx &c, Expr var, const UPoly &A, const UPoly &F,
                         std::vector<Piece> &pieces, std::vector<Expr> &extraTerms,
                         UPoly &certN, UPoly &certD, std::string &reason)
{
    if (A.isZero())
        return true;

    const UPoly dF = F.derivative();
    const UPoly R = resultantT(A, dF, F);
    const UPoly Rsq = R.squarefreePart();

    // Rational residues from the FULL factorization of the squarefree
    // resultant (Zassenhaus): no search budget, nothing missed.
    std::vector<Rational> residues;
    for (const UPoly &fact : factorOverQ(Rsq))
        if (fact.deg() == 1)
            residues.push_back(fact.coeff(0) * Rational(std::int64_t{-1}));

    UPoly leftN = A, leftD = F;
    for (const Rational &res : residues) {
        if (res.isZero())
            continue; // zero-residue poles contribute nothing
        const UPoly v = UPoly::gcd(A - res * dF, F);
        if (v.isConst())
            continue;
        Piece p;
        p.kind = Piece::Log;
        p.coeff = res;
        p.v = v;
        p.scale = R1();
        pieces.push_back(p);
        // left -= res * v'/v
        fracAdd(leftN, leftD, res * Rational(std::int64_t{-1}) * v.derivative(), v);
    }
    if (leftN.isZero())
        return true;

    // Second residue sweep + quadratic residue pair (modular Trager).
    // The squarefree part of res(leftN - t*leftD', leftD) carries the
    // remaining residues: its rational roots are swept as grouped
    // logarithms (zero residues drop out by reducing the fraction),
    // and if the non-rational remainder is exactly an irreducible
    // quadratic c = t^2 + p t + q (degree-2 reducible <=> rational
    // root, so no factorization is needed), all remaining residues are
    // the conjugate roots of c. v = gcd(leftN - t*leftD', leftD) over
    // Q[t]/(c) has coefficients A + t*B, and the conjugate pair sum
    // has a RATIONAL derivative — the certificate stays in Q(x) and
    // the printed coefficients only need Q plus sqrt(p^2 - 4q).
    {
        const UPoly n0 = leftN, d0 = leftD;
        const UPoly dL = d0.derivative();
        UPoly Rsq2 = resultantT(n0, dL, d0).squarefreePart();

        std::vector<Rational> res2;
        const std::vector<UPoly> facts2 = factorOverQ(Rsq2);
        for (const UPoly &fa : facts2)
        for (const UPoly &fact : facts2)
            if (fact.deg() == 1)
                res2.push_back(fact.coeff(0) * Rational(std::int64_t{-1}));
        for (const Rational &res : res2) {
            if (res.isZero())
                continue;
            const UPoly v = UPoly::gcd(n0 - res * dL, d0);
            if (v.isConst())
                continue;
            Piece p;
            p.kind = Piece::Log;
            p.coeff = res;
            p.v = v;
            p.scale = R1();
            pieces.push_back(p);
            fracAdd(leftN, leftD,
                    res * Rational(std::int64_t{-1}) * v.derivative(), v);
        }
        // Zero-residue poles are ballast: reduce the fraction.
        const UPoly g = UPoly::gcd(leftN, leftD);
        if (!g.isConst()) {
            UPoly q, r;
            UPoly::divMod(leftN, g, q, r);
            assert(r.isZero());
            leftN = q;
            UPoly::divMod(leftD, g, q, r);
            assert(r.isZero());
            leftD = q;
        }
        if (leftN.isZero())
            return true;

        // Quadratic residue pairs (modular Trager), one per irreducible
        // quadratic factor of Rsq2. The gcd over Q[t]/(c_i) captures
        // only the poles whose residues are roots of c_i, so factors of
        // other degrees never interfere; degree >= 3 residues need
        // RootOf atoms (item 6c) and are left to the final fallback.
        {
            for (const UPoly &fact : facts2) {
                if (leftN.isZero())
                    break; // everything consumed: further gcd(0 - tS', S)
                           // can be nontrivial in the ring and would
                           // subtract garbage, resurrecting the numerator
                if (fact.deg() != 2)
                    continue;
                UPoly c2 = fact;
                c2.makeMonic();
                const Rational pc = c2.coeff(1);
                const Rational qc = c2.coeff(0);
                const Rational D = pc * pc - Rational(std::int64_t{4}) * qc;
                const UPoly dLpair = leftD.derivative();
                const ModCRing ring(c2);
                const UPoly tEl = ring.reduce(UPoly(std::vector<Rational>{R0(), R1()}));
                const auto lift = [&](const UPoly &q, bool mulT) {
                    std::vector<UPoly> cs;
                    for (std::size_t i = 0; i < q.coeffs().size(); ++i)
                        cs.push_back(mulT ? ring.mul(tEl, UPoly(q.coeff(i)))
                                          : UPoly(q.coeff(i)));
                    return ModCPoly(ring, std::move(cs));
                };
                const ModCPoly v = ModCPoly::gcd(lift(leftN, false) - lift(dLpair, true),
                                                  lift(leftD, false));
                std::vector<Rational> aCs, bCs;
                if (v.deg() >= 1) {
                    for (std::size_t i = 0; i <= static_cast<std::size_t>(v.deg()); ++i) {
                        aCs.push_back(v.coeff(i).coeff(0));
                        bCs.push_back(v.coeff(i).coeff(1));
                    }
                }
                const UPoly Aq(aCs), Bq(bCs);
                if (v.deg() >= 1)
                if (v.deg() < 1 || Bq.isZero())
                    continue;
                const UPoly dA = Aq.derivative(), dB = Bq.derivative();
                if (D.signum() > 0) {
                    // Real pair alpha = u +- sqrt(D)/2, u = -p/2:
                    // contribution = alpha*log(A + alpha B) + conjugate.
                    const Rational u = pc * Rational(std::int64_t{-1}, BigInt(2));
                    const Expr sqrtD = sqrtExpr(c, D);
                    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
                    const Expr alphaE = c.add({c.number(u), c.mul({half, sqrtD})});
                    const Expr betaE = c.add({c.number(u), c.mul({c.neg(half), sqrtD})});
                    const Expr ea = toExpr(c, Aq, var);
                    const Expr eb = toExpr(c, Bq, var);
                    extraTerms.push_back(c.mul(
                        {alphaE, c.func("log", c.add({ea, c.mul({alphaE, eb})}))}));
                    extraTerms.push_back(c.mul(
                        {betaE, c.func("log", c.add({ea, c.mul({betaE, eb})}))}));
                    const UPoly W = Aq * Aq - pc * Aq * Bq + qc * Bq * Bq;
                    const UPoly num =
                        pc * Rational(std::int64_t{-1}) * dA * Aq +
                        Rational(std::int64_t{2}) * qc * dA * Bq +
                        (pc * pc - Rational(std::int64_t{2}) * qc) * Aq * dB -
                        pc * qc * dB * Bq;
                    fracAdd(certN, certD, num, W);
                    fracAdd(leftN, leftD, num * Rational(std::int64_t{-1}), W);
                } else {
                    // Complex pair alpha = u +- i*w, w^2 = -D/4:
                    // u*log(W) + sqrt(-D)*atan(X/Y), X = A + uB, Y = wB.
                    const Rational u = pc * Rational(std::int64_t{-1}, BigInt(2));
                    const Rational w2 = D * Rational(std::int64_t{-1}, BigInt(4));
                    const UPoly X = Aq + u * Bq;
                    const UPoly W = X * X + w2 * Bq * Bq;
                    if (!u.isZero())
                        extraTerms.push_back(c.mul(
                            {c.number(u), c.func("log", toExpr(c, W, var))}));
                    const Expr sqrtNegD = sqrtExpr(c, D * Rational(std::int64_t{-1}));
                    const Expr yE = c.mul({toExpr(c, Bq, var), sqrtExpr(c, w2)});
                    extraTerms.push_back(c.mul(
                        {sqrtNegD,
                         c.func("atan", c.mul({toExpr(c, X, var),
                                               c.pow(yE, c.number(std::int64_t{-1}))}))}));
                    const UPoly num =
                        u * W.derivative() +
                        w2 * Rational(std::int64_t{2}) *
                            (X.derivative() * Bq - X * Bq.derivative());
                    fracAdd(certN, certD, num, W);
                    fracAdd(leftN, leftD, num * Rational(std::int64_t{-1}), W);
                }
            }
            if (leftN.isZero())
                return true;
        }
    }
    return integrateSplitting(leftN, leftD, pieces, reason);
}

} // namespace

// ── Trager resultant by evaluation-interpolation ──────────────

UPoly resultantT(const UPoly &P, const UPoly &Q, const UPoly &M)
{
    assert(!M.isZero());
    const int n = M.deg();
    if (n < 1)
        return UPoly(R1()); // res of anything with a constant is 1 by convention

    std::vector<Rational> ys;
    for (int i = 0; i <= n; ++i) {
        const Rational t(static_cast<std::int64_t>(i));
        ys.push_back(UPoly::resultant(P - t * Q, M));
    }

    // Lagrange interpolation over t = 0..n.
    std::vector<Rational> coeffs(static_cast<std::size_t>(n) + 1, R0());
    for (int i = 0; i <= n; ++i) {
        UPoly num(R1());
        Rational den(R1());
        for (int j = 0; j <= n; ++j) {
            if (j == i)
                continue;
            num = num * UPoly(std::vector<Rational>{
                            Rational(-static_cast<std::int64_t>(j)), R1()});
            den = den * Rational(static_cast<std::int64_t>(i - j));
        }
        const Rational scale = ys[static_cast<std::size_t>(i)] / den;
        for (std::size_t k = 0; k < num.coeffs().size(); ++k)
            coeffs[k] += num.coeff(k) * scale;
    }
    return UPoly(coeffs);
}

// ── Expr <-> Q(x) ─────────────────────────────────────────────

Expr toExpr(Ctx &c, const UPoly &p, Expr var)
{
    std::vector<Expr> terms;
    for (std::size_t k = 0; k < p.coeffs().size(); ++k) {
        if (p.coeff(k).isZero())
            continue;
        if (k == 0)
            terms.push_back(c.number(p.coeff(k)));
        else
            terms.push_back(c.mul({c.number(p.coeff(k)),
                                   c.pow(var, c.number(static_cast<std::int64_t>(k)))}));
    }
    return c.add(terms);
}

bool toRational(Ctx &c, Expr e, Expr var, UPoly &num, UPoly &den)
{
    num = UPoly();
    den = UPoly(R1());
    switch (c.kind(e)) {
    case NodeKind::Number:
        num = UPoly(c.numberValue(e));
        return true;
    case NodeKind::Symbol:
        if (e == var) {
            num = UPoly(std::vector<Rational>{R0(), R1()});
            return true;
        }
        return false;
    case NodeKind::Add: {
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            UPoly n2, d2;
            if (!toRational(c, c.child(e, i), var, n2, d2))
                return false;
            num = num * d2 + n2 * den;
            den = den * d2;
        }
        return true;
    }
    case NodeKind::Mul: {
        num = UPoly(R1());
        den = UPoly(R1());
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            UPoly n2, d2;
            if (!toRational(c, c.child(e, i), var, n2, d2))
                return false;
            num = num * n2;
            den = den * d2;
        }
        return true;
    }
    case NodeKind::Pow: {
        const Expr b = c.child(e, 0), k = c.child(e, 1);
        if (c.kind(k) != NodeKind::Number)
            return false;
        const Rational &kk = c.numberValue(k);
        if (!(kk.den() == BigInt(1)))
            return false;
        std::int64_t ki = 0;
        if (!kk.num().fitsInt64(ki) || ki < -kMaxPowExp || ki > kMaxPowExp)
            return false;
        UPoly bn, bd;
        if (!toRational(c, b, var, bn, bd))
            return false;
        const auto e64 = static_cast<std::uint64_t>(ki < 0 ? -ki : ki);
        if (ki >= 0) {
            num = bn.powUInt(e64);
            den = bd.powUInt(e64);
        } else {
            if (bn.isZero())
                return false;
            num = bd.powUInt(e64);
            den = bn.powUInt(e64);
        }
        return true;
    }
    case NodeKind::Func:
        return false;
    }
    return false;
}

// ── Hermite reduction ─────────────────────────────────────────

HermiteResult hermiteReduce(const UPoly &N0, const UPoly &D0)
{
    assert(!D0.isZero());
    HermiteResult out;
    out.rd = UPoly(R1());
    out.S = UPoly(R1());

    if (N0.isZero())
        return out;

    // Polynomial part: its antiderivative joins the rational part.
    UPoly pq, pr;
    UPoly::divMod(N0, D0, pq, pr);
    out.rn = polyIntegral(pq);
    if (pr.isZero()) {
        out.gn = UPoly();
        return out;
    }

    // Work with the monic associate of D: D = lc * prod F_i^i.
    const std::vector<UPoly> fs = D0.squarefreeDecomposition();
    const UPoly N = pr * (R1() / D0.lc());

    std::vector<UPoly> Ps;
    for (std::size_t i = 0; i < fs.size(); ++i) {
        Ps.push_back(fs[i].powUInt(i + 1));
        out.S = out.S * fs[i];
    }
    const std::vector<UPoly> Bs = partialFractions(N, Ps);

    out.gn = UPoly();
    for (std::size_t idx = 0; idx < fs.size(); ++idx) {
        const UPoly &F = fs[idx];
        const int mult = static_cast<int>(idx) + 1;
        const UPoly dF = F.derivative();

        // Peel B into level numerators A_j (j = mult..1).
        std::vector<UPoly> A(static_cast<std::size_t>(mult) + 1);
        UPoly B = Bs[idx];
        for (int j = mult; j >= 1; --j) {
            UPoly q, r;
            UPoly::divMod(B, F, q, r);
            A[static_cast<std::size_t>(j)] = r;
            B = q;
        }

        for (int j = mult; j >= 2; --j) {
            // A[j]/F^j = (C/F^(j-1))' + A2/F^(j-1) with
            // C = -A[j] * inv((j-1) * F' mod F) mod F.
            const UPoly coef = dF * Rational(static_cast<std::int64_t>(j - 1));
            const UPoly C = pmod(A[static_cast<std::size_t>(j)] * Rational(std::int64_t{-1}) *
                                     UPoly::invMod(coef % F, F),
                                 F);

            const UPoly Fjm1 = F.powUInt(static_cast<std::uint64_t>(j - 1));
            out.rn = out.rn * Fjm1 + out.rd * C;
            out.rd = out.rd * Fjm1;

            const UPoly rhs = A[static_cast<std::size_t>(j)] -
                              (C.derivative() * F -
                               Rational(static_cast<std::int64_t>(j - 1)) * C * dF);
            UPoly q, r;
            UPoly::divMod(rhs, F, q, r);
            assert(r.isZero());
            A[static_cast<std::size_t>(j - 1)] = A[static_cast<std::size_t>(j - 1)] + q;
        }

        // g += A[1] * (S / F).
        UPoly q, r;
        UPoly::divMod(out.S, F, q, r);
        out.gn = out.gn + A[1] * q;
    }
    return out;
}

// ── Full integration with certificate ─────────────────────────

RationalIntegral integrateRational(Ctx &c, Expr f, Expr var)
{
    RationalIntegral out;
    UPoly N, D;
    if (!toRational(c, f, var, N, D)) {
        out.reason = "integrand is not a rational function of the variable";
        return out;
    }
    if (D.isZero()) {
        out.reason = "zero denominator";
        return out;
    }
    if (N.isZero()) {
        out.status = RationalIntegral::Status::ProvedSymbolic;
        out.F = c.zero();
        return out;
    }

    const HermiteResult h = hermiteReduce(N, D);

    // Split the squarefree residual over its factors.
    const std::vector<UPoly> fs = D.squarefreeDecomposition();
    std::vector<UPoly> sq;
    for (const UPoly &F : fs)
        if (!F.isConst())
            sq.push_back(F);
    const std::vector<UPoly> gs = sq.empty() ? std::vector<UPoly>()
                                             : partialFractions(h.gn, sq);

    std::vector<Piece> pieces;
    std::vector<Expr> extraTerms;
    UPoly qcertN, qcertD(R1());
    for (std::size_t i = 0; i < sq.size(); ++i) {
        if (gs[i].isZero())
            continue;
        if (!integrateSquarefree(c, var, gs[i], sq[i], pieces, extraTerms,
                                 qcertN, qcertD, out.reason))
            return out;
    }

    // Certificate (Tier-1, PROVED_SYMBOLIC): the exact derivatives of all
    // constructed pieces must sum to the integrand in Q(x).
    UPoly vn = h.rn.derivative() * h.rd - h.rn * h.rd.derivative();
    UPoly vd = h.rd * h.rd;
    for (const Piece &p : pieces) {
        if (p.kind == Piece::Log)
            fracAdd(vn, vd, p.coeff * p.v.derivative(), p.v);
        else
            fracAdd(vn, vd, p.coeff * p.scale * p.v.derivative(),
                    p.v * p.v + UPoly(p.scale * p.scale));
    }
    fracAdd(vn, vd, qcertN, qcertD);
    if (!(vn * D == vd * N)) {
        out.reason = "internal certificate check failed";
        return out;
    }

    // Assemble the antiderivative.
    std::vector<Expr> terms;
    if (!h.rn.isZero())
        terms.push_back(c.mul({toExpr(c, h.rn, var),
                               c.pow(toExpr(c, h.rd, var), c.number(std::int64_t{-1}))}));
    for (const Piece &p : pieces) {
        if (p.kind == Piece::Log) {
            terms.push_back(c.mul({c.number(p.coeff),
                                   c.func("log", toExpr(c, p.v, var))}));
        } else {
            const Expr arg = c.mul({toExpr(c, p.v, var),
                                    c.pow(c.number(p.scale), c.number(std::int64_t{-1}))});
            terms.push_back(c.mul({c.number(p.coeff), c.func("atan", arg)}));
        }
    }
    for (const Expr &t : extraTerms)
        terms.push_back(t);
    out.F = c.add(terms);
    out.status = RationalIntegral::Status::ProvedSymbolic;
    out.reason.clear();
    return out;
}

} // namespace numkit::cas
