#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/integrate/verify.hpp>

#include <numkit/cas/core/series.hpp>
#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/cas/poly/modcpoly.hpp>
#include <numkit/cas/poly/solve.hpp>
#include <numkit/cas/poly/sturm.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>
#include <numkit/cas/rubi/rules.hpp>

#include <algorithm>
#include <cassert>
#include <cmath>
#include <numeric>
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

// Power sums s_k = sum of k-th powers of the roots of the MONIC poly
// c (ascending coeffs), for k = 0..deg-1, by Newton's identities.
std::vector<Rational> newtonPowerSums(const std::vector<Rational> &c)
{
    const int d = static_cast<int>(c.size()) - 1;
    std::vector<Rational> s;
    s.push_back(Rational(static_cast<std::int64_t>(d))); // s_0 = d
    for (int k = 1; k < d; ++k) {
        // Newton: s_k = -(c_{d-1} s_{k-1} + ... + c_{d-k+1} s_1)
        //               - k * c_{d-k}   (k <= d)
        Rational acc = Rational(static_cast<std::int64_t>(k)) *
                       c[static_cast<std::size_t>(d - k)];
        for (int i = 1; i < k; ++i)
            acc = acc + c[static_cast<std::size_t>(d - i)] *
                            s[static_cast<std::size_t>(k - i)];
        s.push_back(acc * Rational(std::int64_t{-1}));
    }
    return s;
}

// Trace of a field element given by its t-coordinates (deg < d).
Rational fieldTrace(const UPoly &p, const std::vector<Rational> &s)
{
    Rational acc(std::int64_t{0});
    for (std::size_t j = 0; j < p.coeffs().size() && j < s.size(); ++j)
        acc = acc + p.coeff(j) * s[j];
    return acc;
}

// Exact Lagrange interpolation over the rationals: the unique
// polynomial of degree < xs.size() through the given points.
UPoly interpolateRational(const std::vector<Rational> &xs,
                          const std::vector<Rational> &ys)
{
    assert(xs.size() == ys.size());
    std::vector<Rational> coeffs(xs.size(), R0());
    for (std::size_t i = 0; i < xs.size(); ++i) {
        if (ys[i].isZero())
            continue;
        Rational den(R1());
        UPoly num(R1());
        for (std::size_t j = 0; j < xs.size(); ++j) {
            if (j == i)
                continue;
            num = num * UPoly(std::vector<Rational>{Rational(-xs[j]), R1()});
            den = den * (xs[i] - xs[j]);
        }
        const Rational scale = ys[i] / den;
        for (std::size_t k = 0; k < num.coeffs().size() && k < coeffs.size(); ++k)
            coeffs[k] = coeffs[k] + num.coeff(k) * scale;
    }
    return UPoly(coeffs);
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

bool checkBudget(const Ctx &c, Budget *budget, std::string &reason)
{
    if (!budget)
        return true;
    if (!budget->step()) {
        reason = "step budget exhausted";
        return false;
    }
    if (!budget->recordArenaBytes(c.nodeCount() * 32)) {
        reason = "arena byte budget exhausted";
        return false;
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
                         UPoly &certN, UPoly &certD, std::string &reason,
                         Budget *budget)
{
    if (A.isZero())
        return true;
    if (!checkBudget(c, budget, reason))
        return false;

    const UPoly dF = F.derivative();
    const UPoly R = resultantT(A, dF, F);
    const UPoly Rsq = R.squarefreePart();

    // Rational residues from the FULL factorization of the squarefree
    // resultant (Zassenhaus): no search budget, nothing missed.
    std::vector<Rational> residues;
    for (const UPoly &fact : factorOverQ(Rsq, budget))
        if (fact.deg() == 1)
            residues.push_back(fact.coeff(0) * Rational(std::int64_t{-1}));
    if (budget && !budget->ok()) {
        reason = budget->status() == BudgetStatus::StepExhausted
                     ? "step budget exhausted"
                     : "arena byte budget exhausted";
        return false;
    }

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
        const std::vector<UPoly> facts2 = factorOverQ(Rsq2, budget);
        if (budget && !budget->ok()) {
            reason = budget->status() == BudgetStatus::StepExhausted
                         ? "step budget exhausted"
                         : "arena byte budget exhausted";
            return false;
        }
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
                const ModCPoly v =
                    ModCPoly::gcd(lift(leftN, false) - lift(dLpair, true),
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

        // Trager over RootOf atoms: EVERY irreducible factor c of degree
        // >= 3. For each: v = gcd(A - t*S', S) over Q[t]/(c) captures the
        // poles with residues among c's conjugate roots; conjugate
        // evaluation of the same v yields every pole's factor via the
        // Galois automorphism. The answer terms are
        // RootOf(c, i) * log(v(x, RootOf(c, i))) with integer powers of
        // the atom. The contribution's derivative is the field trace
        // Tr(t * v' * v^-1) = P(x)/Q(x) with Q = Norm(v) — BOTH
        // reconstructed by exact rational interpolation in x, so
        // subtracting P/Q from the running fraction and adding it to
        // the certificate keeps the STANDARD arithmetic gate
        // sufficient (no gateProven bypass needed).
        for (const UPoly &fact : facts2) {
            if (fact.deg() < 3 || leftN.isZero())
                continue;
            if (!checkBudget(c, budget, reason))
                return false;
            const int d = fact.deg();
            const std::vector<Rational> s = newtonPowerSums(fact.coeffs());
            const ModCRing ring(fact);
            const UPoly tEl = ring.reduce(UPoly(std::vector<Rational>{R0(), R1()}));
            const auto lift = [&](const UPoly &q, bool mulT) {
                std::vector<UPoly> cs;
                for (std::size_t i = 0; i < q.coeffs().size(); ++i)
                    cs.push_back(mulT ? ring.mul(tEl, UPoly(q.coeff(i)))
                                      : UPoly(q.coeff(i)));
                return ModCPoly(ring, std::move(cs));
            };
            const UPoly dL3 = leftD.derivative();
            const ModCPoly v =
                ModCPoly::gcd(lift(leftN, false) - lift(dL3, true),
                              lift(leftD, false));
            if (v.deg() < 1)
                continue;

            // Interpolation degrees, tight: Q = Norm(v) has
            // deg_x Q = d * deg_x v, and the numerator P = T*Q where
            // every summand of T = Tr(t*v'*v^-1) has degree
            // (deg v - 1) + (d-1)*deg v = d*deg v - 1, so
            // deg P <= 2*d*deg v - 1. The old bound 2*d*deg(leftD) + ...
            // paid for the WHOLE denominator even when v captures a
            // single pole — 24 interpolation points where 7 suffice,
            // each point costing a Q-resultant plus a ring inversion.
            const int qDeg = d * v.deg();
            const int pDeg = 2 * d * v.deg() - 1;
            const int need = (qDeg > pDeg ? qDeg : pDeg) + 1;
            std::vector<Rational> xs, qs, ps;
            for (int x0 = 1; static_cast<int>(xs.size()) < need && x0 < 6 * need + 10; ++x0) {
                const Rational x0r(static_cast<std::int64_t>(x0));
                // v(x0, t) as a plain Q[t] polynomial (degree < d in t)
                // for the norm resultant, and simultaneously as a ring
                // element u: v's coefficients are already in normal
                // form, so scaling by x0^k and adding stays there — no
                // Euclidean reduction of the tall uPlain needed.
                UPoly uPlain = ring.zero();
                UPoly u = ring.zero();
                Rational pw(1);
                for (std::size_t k = 0; k <= static_cast<std::size_t>(v.deg()); ++k) {
                    const UPoly rk = v.coeff(k);
                    if (!rk.isZero()) {
                        uPlain = uPlain + rk * UPoly(pw);
                        u = ring.add(u, ring.mul(rk, UPoly(pw)));
                    }
                    pw = pw * x0r;
                }
                // Q(x0) = Norm = res_t(v(x0,t), c)
                const Rational qv = UPoly::resultant(uPlain, fact);
                if (qv.isZero())
                    continue; // v(x0,t) shares a root with c: skip
                // T(x0) = Tr(t * v'(x0,t) / v(x0,t))
                UPoly du = ring.zero();
                pw = Rational(1);
                for (std::size_t k = 0; k <= static_cast<std::size_t>(v.deg()); ++k) {
                    const UPoly rk = v.coeff(k);
                    if (!rk.isZero() && k >= 1)
                        du = ring.add(du, ring.mul(rk, UPoly(Rational(
                            static_cast<std::int64_t>(k) * pw / x0r))));
                    pw = pw * x0r;
                }
                const UPoly q3 = ring.mul(tEl, ring.mul(du, ring.inv(u)));
                const Rational tTrace = fieldTrace(q3, s);
                xs.push_back(x0r);
                qs.push_back(qv);
                ps.push_back(tTrace * qv);
            }
            if (static_cast<int>(xs.size()) < need) {
                reason = "degree >= 3 factor: not enough interpolation points";
                return false;
            }
            const UPoly Qpoly = interpolateRational(xs, qs);
            const UPoly Ppoly = interpolateRational(xs, ps);
            if (Qpoly.isZero()) {
                reason = "degree >= 3 factor: vanishing norm";
                return false;
            }

            fracAdd(certN, certD, Ppoly, Qpoly);
            fracAdd(leftN, leftD, Ppoly * Rational(std::int64_t{-1}), Qpoly);

            // Emission. Rioboo real forms, phase A (item 7): for an
            // irreducible CUBIC with exactly one real root rho, the
            // conjugate pair alpha, alpha-bar of the two complex
            // roots contributes, with s1 = alpha+alpha-bar = -p-rho,
            // s2 = alpha*alpha-bar = -s/rho (both in Q[rho]) and
            // w2 = (4 s2 - s1^2)/4 > 0, b = sqrt(w2):
            //   alpha*log v(x,alpha) + conjugate
            //     = (s1/2)*log(R^2 + w2*I^2) - 2b*atan(b*I/R),
            // where v(x,alpha) = R(x) + i*b*I(x) and R, I lie in
            // Q[rho][x]: with w_k(t) = a2 t^2 + a1 t + a0 (the
            // x^k coefficient of v), Re(w_k(alpha)) =
            // a2(s1^2-2s2)/2 + a1 s1/2 + a0 and
            // Im(w_k(alpha)) = b*(a2 s1 + a1) - both in Q[rho].
            // No Q-bar layer: everything is Q[t]/(c) ring arithmetic
            // plus a Sturm root count. The certificate stays the
            // rational Norm/Trace subtraction above (the trace of
            // the WHOLE contribution); the form merely becomes real.
            bool riobooPair = false;
            if (d == 3) {
                const std::vector<RootInterval> rts =
                    isolateRealRoots(fact);
                if (rts.size() == 1)
                    riobooPair = true;
            }
            const auto ringToExpr = [&](const UPoly &e, const Expr &atom) {
                std::vector<Expr> terms;
                for (std::size_t j = 0; j < e.coeffs().size(); ++j)
                    if (!e.coeff(j).isZero())
                        terms.push_back(j == 0
                            ? c.number(e.coeff(j))
                            : c.mul({c.number(e.coeff(j)),
                                     c.pow(atom, c.number(
                                         static_cast<std::int64_t>(j)))}));
                if (terms.empty())
                    return c.zero();
                return c.add(terms);
            };
            const auto polyInXExpr =
                [&](const std::vector<UPoly> &ringCoeffs, const Expr &atom) {
                std::vector<Expr> terms;
                for (std::size_t k = 0; k < ringCoeffs.size(); ++k) {
                    if (ringCoeffs[k].isZero())
                        continue;
                    const Expr ck = ringToExpr(ringCoeffs[k], atom);
                    if (k == 0)
                        terms.push_back(ck);
                    else
                        terms.push_back(c.mul({ck, c.pow(var, c.number(
                            static_cast<std::int64_t>(k)))}));
                }
                if (terms.empty())
                    return c.zero();
                return c.add(terms);
            };
            const auto mentionsNonConst = [&](const Expr &arg) {
                if (c.kind(arg) == NodeKind::Symbol)
                    return true;
                for (std::size_t ai = 0; ai < c.childCount(arg); ++ai)
                    if (c.kind(c.child(arg, ai)) != NodeKind::Number &&
                        c.kind(c.child(arg, ai)) != NodeKind::RootOf)
                        return true;
                return false;
            };

            if (riobooPair) {
                const Expr rho = c.rootOf(fact.coeffs(), 0); // unique
                const Rational cp = fact.coeff(2), cs = fact.coeff(0);
                // ring elements of Q[rho]: s1 = -p - rho, s2 = -s/rho
                const UPoly s1({Rational(-cp), Rational(std::int64_t{-1})});
                const UPoly tEl2 = ring.reduce(
                    UPoly(std::vector<Rational>{R0(), R1()}));
                const UPoly s2 = ring.mul(UPoly(Rational(-cs)),
                                           ring.inv(tEl2));
                const UPoly half(Rational(std::int64_t{1}, BigInt(2)));
                const UPoly quarter(Rational(std::int64_t{1}, BigInt(4)));
                const UPoly four(Rational(std::int64_t{4}));
                const UPoly two(Rational(std::int64_t{2}));
                const UPoly w2 = ring.mul(
                    ring.add(ring.mul(four, s2), ring.neg(ring.mul(s1, s1))),
                    quarter);
                // R(x), I(x) with Q[rho] coefficients:
                // Re(w_k) = a2*(s1^2-2s2)/2 + a1*s1/2 + a0
                // Im(w_k)/b = a2*s1 + a1
                std::vector<UPoly> Rk(v.deg() + 1), Ik(v.deg() + 1);
                for (int k = 0; k <= v.deg(); ++k) {
                    const UPoly wk = v.coeff(static_cast<std::size_t>(k));
                    const UPoly wa2(wk.coeff(2)), wa1(wk.coeff(1));
                    const UPoly term1 = ring.mul(
                        wa2, ring.mul(half, ring.sub(ring.mul(s1, s1),
                                                     ring.mul(two, s2))));
                    const UPoly term2 = ring.mul(wa1,
                                                 ring.mul(half, s1));
                    Rk[k] = ring.add(ring.add(term1, term2),
                                     UPoly(wk.coeff(0)));
                    Ik[k] = ring.add(ring.mul(wa2, s1), wa1);
                }
                // real-root term rho * log(v(x, rho))
                std::vector<Expr> argTerms;
                for (int k = 0; k <= v.deg(); ++k) {
                    const UPoly rk = v.coeff(static_cast<std::size_t>(k));
                    if (rk.isZero())
                        continue;
                    const Expr ck = ringToExpr(rk, rho);
                    if (k == 0)
                        argTerms.push_back(ck);
                    else
                        argTerms.push_back(c.mul({ck, c.pow(var,
                            c.number(static_cast<std::int64_t>(k)))}));
                }
                if (!argTerms.empty()) {
                    const Expr arg = c.add(argTerms);
                    if (mentionsNonConst(arg))
                        extraTerms.push_back(
                            c.mul({rho, c.func("log", arg)}));
                }
                // N2 = R^2 + w2 I^2 (convolution in the ring)
                std::vector<UPoly> N2(2 * v.deg() + 1, ring.zero());
                for (int i = 0; i <= v.deg(); ++i)
                    for (int j = 0; j <= v.deg(); ++j) {
                        N2[i + j] = ring.add(N2[i + j],
                                             ring.add(ring.mul(Rk[i], Rk[j]),
                                                      ring.mul(w2,
                                                          ring.mul(Ik[i],
                                                                   Ik[j]))));
                    }
                const Expr n2Expr = polyInXExpr(N2, rho);
                if (mentionsNonConst(n2Expr))
                    extraTerms.push_back(c.mul(
                        {ringToExpr(ring.mul(s1, half), rho),
                         c.func("log", n2Expr)}));
                // -2 b atan(b I / R), b = sqrt(w2)
                const Expr rExpr = polyInXExpr(Rk, rho);
                const Expr iExpr = polyInXExpr(Ik, rho);
                const Expr bExpr = c.pow(ringToExpr(w2, rho),
                                         c.number(Rational(
                                             std::int64_t{1}, BigInt(2))));
                if (mentionsNonConst(rExpr) && !c.isZero(rExpr)) {
                    const Expr atanArg = c.mul({bExpr, c.mul(
                        {iExpr, c.pow(rExpr, c.number(std::int64_t{-1}))})});
                    extraTerms.push_back(c.mul(
                        {c.number(std::int64_t{-2}), bExpr,
                         c.func("atan", atanArg)}));
                }
            } else {
                // general d: emit sum_i RootOf(c, i) * log(v(x, ...))
                for (int i = 0; i < d; ++i) {
                    const Expr rootExpr = c.rootOf(fact.coeffs(), i);
                    std::vector<Expr> argTerms;
                    for (std::size_t k = 0;
                         k <= static_cast<std::size_t>(v.deg()); ++k) {
                        const UPoly rk = v.coeff(k);
                        if (rk.isZero())
                            continue;
                        const Expr ck = ringToExpr(rk, rootExpr);
                        if (k == 0)
                            argTerms.push_back(ck);
                        else
                            argTerms.push_back(c.mul({ck,
                                c.pow(var, c.number(
                                    static_cast<std::int64_t>(k)))}));
                    }
                    if (argTerms.empty())
                        continue;
                    const Expr arg = c.add(argTerms);
                    if (!mentionsNonConst(arg))
                        continue; // constant log drops into C
                    extraTerms.push_back(
                        c.mul({rootExpr, c.func("log", arg)}));
                }
            }
        }
        if (leftN.isZero())
            return true;
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

// ── Rational functions of exp: the first Liouvillian step (C3 spike)
//
// Integrand rational in exp(x) integrates via t = e^x: dx = dt/t,
// so integral of R(e^x) dx becomes integral of R(t)/t dt — the whole
// rational kernel (Hermite, Trager, certificates) is reused verbatim
// in the t-world, the antiderivative is back-substituted t -> exp(x),
// and the gate is exact: d/dx of the answer must equal the integrand
// node-for-node (hash-consing makes the comparison structural).

namespace {

// Rebuild `e` replacing every exp(var) node with the symbol `t`.
// Sets ok = false on a bare `var` occurrence (the integrand then
// mixes x outside exp and is not rational in e^x).
Expr substituteExpVar(Ctx &c, Expr e, Expr var, Expr t, bool &ok)
{
    if (e == var) {
        ok = false;
        return e;
    }
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func:
        if (c.funcName(e) == "exp") {
            const Expr arg = c.child(e, 0);
            if (arg == var)
                return t;
            // exp(k*x) with an INTEGER k is t^k (rational in t);
            // anything else (k*x + b, fractional k, x^2) leaves var
            // in the tree and fails the substitution honestly.
            UPoly an, ad;
            if (toRational(c, arg, var, an, ad) && an.deg() == 1 &&
                an.coeff(0).isZero() && ad.isConst()) {
                const Rational k = an.lc() / ad.coeff(0);
                if (k.den() == BigInt(1))
                    return c.pow(t, c.number(k));
            }
        }
        return c.func(c.funcName(e),
                      substituteExpVar(c, c.child(e, 0), var, t, ok));
    case NodeKind::Pow:
        return c.pow(substituteExpVar(c, c.child(e, 0), var, t, ok),
                     substituteExpVar(c, c.child(e, 1), var, t, ok));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(substituteExpVar(c, c.child(e, i), var, t, ok));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

// Rebuild `e` replacing the symbol `t` with exp(var).
Expr substituteBack(Ctx &c, Expr e, Expr t, Expr expVar)
{
    if (e == t)
        return expVar;
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func:
        return c.func(c.funcName(e),
                      substituteBack(c, c.child(e, 0), t, expVar));
    case NodeKind::Pow:
        return c.pow(substituteBack(c, c.child(e, 0), t, expVar),
                     substituteBack(c, c.child(e, 1), t, expVar));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(substituteBack(c, c.child(e, i), t, expVar));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

} // namespace

// ── Rational functions of log: the second Liouvillian storey ──
//
// t = log x gives dt = dx/x, so integral of R(log x)/x dx becomes
// integral of R(t) dt — again the whole rational kernel in the
// t-world. Legality check is canonical: after replacing log(x)
// nodes with t, the product f*x must not mention x anymore (then
// f = R(t)/x exactly; anything else mixes x beyond the Jacobian and
// this storey declines). The gate is the structural ROUND-TRIP: the
// answer F = r.F(log x) contains no bare x by construction, so
// log-substituting it must return r.F; the t-derivative identity is
// the kernel's own Tier-1 certificate and the chain rule closes
// d/dx F = R(log x)/x = f. (No polynomial-gate level here: the x-
// derivative necessarily carries the 1/x factor and is not
// rational in t.)

namespace {

// Rebuild `e` replacing every log(var) node with the symbol `t`.
// Bare `var` occurrences SURVIVE (the 1/x Jacobian needs x); the
// caller checks they cancel.
Expr substituteLogVar(Ctx &c, Expr e, Expr var, Expr t)
{
    if (c.kind(e) == NodeKind::Func && c.funcName(e) == "log" &&
        c.child(e, 0) == var)
        return t;
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func:
        return c.func(c.funcName(e),
                      substituteLogVar(c, c.child(e, 0), var, t));
    case NodeKind::Pow:
        return c.pow(substituteLogVar(c, c.child(e, 0), var, t),
                     substituteLogVar(c, c.child(e, 1), var, t));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(substituteLogVar(c, c.child(e, i), var, t));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

bool mentionsVar(const Ctx &c, Expr e, Expr var)
{
    if (e == var)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        if (mentionsVar(c, c.child(e, i), var))
            return true;
    return false;
}

} // namespace

static RationalIntegral integrateLogRational(Ctx &c, Expr f, Expr var,
                                             Budget *budget)
{
    RationalIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    const Expr t = c.symbol("#l");
    const Expr g = substituteLogVar(c, f, var, t);
    const Expr gx = c.mul({g, var}); // canonical: x*x^-1 folds away
    if (mentionsVar(c, gx, var)) {
        out.reason = "integrand is not R(log(var))/var";
        return out;
    }
    const RationalIntegral r = integrateRational(c, gx, t, budget);
    if (!r.proved()) {
        out.reason = (budget && !budget->ok()) ? r.reason
                                               : "log substitution: " + r.reason;
        return out;
    }
    const Expr logVar = c.func("log", var);
    const Expr F = substituteBack(c, r.F, t, logVar);
    bool ok = true;
    // F has no bare x (r.F is rational in t only), so this forward
    // substitution is exact and must reconstruct the kernel answer.
    if (substituteLogVar(c, F, var, t) != r.F) {
        out.reason = "log substitution certificate failed";
        return out;
    }
    (void)ok;
    out.F = F;
    out.status = RationalIntegral::Status::ProvedSymbolic;
    return out;
}

static RationalIntegral integrateExpRational(Ctx &c, Expr f, Expr var,
                                             Budget *budget)
{
    RationalIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    // The '#e' name is unreachable from the parser grammar, so the
    // substitution symbol can never collide with user symbols.
    const Expr t = c.symbol("#e");
    bool ok = true;
    const Expr g = substituteExpVar(c, f, var, t, ok);
    if (!ok) {
        out.reason = "integrand mixes the variable outside exp(var)";
        return out;
    }
    const RationalIntegral r = integrateRational(c, c.div(g, t), t, budget);
    if (!r.proved()) {
        out.reason = (budget && !budget->ok()) ? r.reason
                                               : "exp substitution: " + r.reason;
        return out;
    }
    const Expr expVar = c.func("exp", var);
    const Expr F = substituteBack(c, r.F, t, expVar);
    // Primary gate: d/dx F(e^x) is rational in t = e^x, so exact
    // verification rationalizes both sides and compares POLYNOMIALS
    // (structural Expr equality is too weak: the derivative comes
    // back as 1 - t/(1+t), canonically unequal to 1/(1+t) until put
    // over a common denominator). Atan answers carry IRRATIONAL
    // constants (sqrt of the pair discriminant) which toRational
    // cannot swallow; there the fallback gate is the exact structural
    // ROUND-TRIP — exp-substituting F must return r.F — while the
    // t-world identity d/dt r.F = g/t is the kernel's own Tier-1
    // certificate and the chain rule closes d/dx F(e^x) = f.
    UPoly n1, d1, n2, d2;
    const Expr dFT = substituteExpVar(c, c.diff(F, var), var, t, ok);
    const bool polyGate =
        ok && toRational(c, dFT, t, n1, d1) && toRational(c, g, t, n2, d2) &&
        n1 == n2 && d1 == d2;
    if (!polyGate) {
        bool ok2 = true;
        if (substituteExpVar(c, F, var, t, ok2) != r.F || !ok2) {
            out.reason = "exp substitution certificate failed";
            return out;
        }
    }
    out.F = F;
    out.status = RationalIntegral::Status::ProvedSymbolic;
    return out;
}

// ── Rational functions of sin/cos: the trigonometric storey ──
//
// The universal substitution t = tan(x/2) rationalizes any rational
// function of sin x and cos x: sin = 2t/(1+t^2), cos = (1-t^2)/(1+t^2),
// dx = 2 dt/(1+t^2). The rational kernel runs in the t-world, the
// answer goes back as t -> tan(x/2). Gate mirrors the exp storey:
// the x-derivative stays rational in t (the Jacobian is rational),
// so the primary check is the POLYNOMIAL identity after forward
// substitution, with the structural round-trip as fallback.

namespace {

// Two-letter trig shorthands keep the table below readable.
Expr halfArg(Ctx &c, Expr var)
{
    return c.mul({c.number(Rational(std::int64_t{1}, BigInt(2))), var});
}

// Rebuild `e` with trig nodes of the variable replaced by rational
// expressions in t = tan(x/2). tan(var/2) itself maps to t — that is
// the substitution point, and recognizing it on the way back is what
// makes the round-trip gate exact. Anything else mentioning var
// (sin(2x), sin(x^2), bare x) sets ok = false: this storey only
// takes integrands rational in sin(x)/cos(x)/tan(x) etc.
Expr substituteTangent(Ctx &c, Expr e, Expr var, Expr t, bool &ok)
{
    if (e == var) {
        ok = false; // bare x: not rational in sin/cos alone
        return e;
    }
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        const std::string &name = c.funcName(e);
        const Expr arg = c.child(e, 0);
        if (arg == var) {
            const Expr one = c.one();
            const Expr t2 = c.add({one, c.pow(t, c.number(std::int64_t{2}))});
            const Expr one_t2 =
                c.add({c.one(), c.neg(c.pow(t, c.number(std::int64_t{2})))});
            const Expr twoT = c.mul({c.number(std::int64_t{2}), t});
            if (name == "sin")
                return c.div(twoT, t2);
            if (name == "cos")
                return c.div(one_t2, t2);
            if (name == "tan")
                return c.div(twoT, one_t2);
            if (name == "cot")
                return c.div(one_t2, twoT);
            if (name == "sec")
                return c.div(t2, one_t2);
            if (name == "csc")
                return c.div(t2, twoT);
        }
        // tan(x/2) IS the substitution variable.
        if (name == "tan" && arg == halfArg(c, var))
            return t;
        return c.func(name, substituteTangent(c, arg, var, t, ok));
    }
    case NodeKind::Pow:
        return c.pow(substituteTangent(c, c.child(e, 0), var, t, ok),
                     substituteTangent(c, c.child(e, 1), var, t, ok));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(substituteTangent(c, c.child(e, i), var, t, ok));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

} // namespace

// ── Radical storey: rational functions of x^(p/q) ──
//
// t = x^(1/L) with L the lcm of all fractional exponents of the
// variable: every x^(p/q) becomes t^(p*L/q) with an INTEGER power
// and bare x becomes t^L, so the integrand turns into a rational
// function of t; the Jacobian dx = L*t^(L-1) dt attaches as a
// factor, the rational kernel runs in the t-world and the answer is
// back-substituted t -> x^(1/L).

namespace {

// First pass: the lcm L of the denominators of all rational
// exponents on Pow(var, r) nodes. Bare var counts as exponent 1/1.
// Returns -1 when var appears anywhere else (inside functions, as
// an exponent itself, under a non-Number power like x^x) or when L
// would exceed 60 (degree blow-up guard): the storey declines.
int radicalIndex(const Ctx &c, Expr e, Expr var)
{
    if (e == var)
        return 1; // x = x^(1/1): legal, no fractional contribution
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return 1;
    case NodeKind::Pow: {
        if (c.child(e, 0) == var) {
            if (c.kind(c.child(e, 1)) != NodeKind::Number)
                return -1; // x^(non-number): x^x, x^sin(x)...
            std::int64_t q64 = 0;
            if (!c.numberValue(c.child(e, 1)).den().fitsInt64(q64) ||
                q64 <= 0 || q64 > 60)
                return -1;
            return static_cast<int>(q64);
        }
        // Other bases may themselves carry radicals (the base is
        // recursed and contributes its lcm); the EXPONENT must not
        // mention the variable at all.
        if (mentionsVar(c, c.child(e, 1), var))
            return -1;
        return radicalIndex(c, c.child(e, 0), var);
    }
    case NodeKind::Func:
    case NodeKind::Add:
    case NodeKind::Mul: {
        int l = 1;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const int q = radicalIndex(c, c.child(e, i), var);
            if (q < 0)
                return -1;
            const int64_t lcm64 = std::lcm(static_cast<int64_t>(l),
                                           static_cast<int64_t>(q));
            if (lcm64 > 60)
                return -1;
            l = static_cast<int>(lcm64);
        }
        return l;
    }
    }
    return -1;
}

// Second pass: rebuild with t = var^(1/L): Pow(var, p/q) maps to
// t^(p*L/q) (integer exponent), bare var to t^L.
Expr radicalRebuild(Ctx &c, Expr e, Expr var, Expr t, int L)
{
    if (e == var)
        return c.pow(t, c.number(static_cast<std::int64_t>(L)));
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Pow: {
        if (c.child(e, 0) == var &&
            c.kind(c.child(e, 1)) == NodeKind::Number) {
            const Rational &r = c.numberValue(c.child(e, 1));
            std::int64_t q64 = 0;
            r.den().fitsInt64(q64);
            const Rational total =
                r * Rational(BigInt(static_cast<std::int64_t>(L)), BigInt(1));
            return c.pow(t, c.number(total)); // total has denominator 1
        }
        return c.pow(radicalRebuild(c, c.child(e, 0), var, t, L),
                     radicalRebuild(c, c.child(e, 1), var, t, L));
    }
    case NodeKind::Func:
        return c.func(c.funcName(e),
                      radicalRebuild(c, c.child(e, 0), var, t, L));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> kids;
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(radicalRebuild(c, c.child(e, i), var, t, L));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    }
    return e;
}

} // namespace

static RationalIntegral integrateRadicalRational(Ctx &c, Expr f, Expr var,
                                                 Budget *budget)
{
    RationalIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    const int L = radicalIndex(c, f, var);
    if (L < 2) {
        // L == 1: a plain rational (the old path owns it); L < 0:
        // the variable escapes the x^(p/q) shape.
        out.reason = L < 0
                         ? "integrand is not rational in a fractional power of the variable"
                         : "integrand has no fractional powers";
        return out;
    }
    const Expr t = c.symbol("#r");
    const Expr g = radicalRebuild(c, f, var, t, L);
    // Jacobian dx = L * t^(L-1) dt.
    const RationalIntegral r = integrateRational(
        c, c.mul({c.number(Rational(
                            BigInt(static_cast<std::int64_t>(L)), BigInt(1))),
                  c.pow(t, c.number(static_cast<std::int64_t>(L - 1))), g}),
        t, budget);
    if (!r.proved()) {
        out.reason = (budget && !budget->ok())
                         ? r.reason
                         : "radical substitution: " + r.reason;
        return out;
    }
    const Expr root = c.pow(var, c.number(
                                  Rational(BigInt(1),
                                           BigInt(static_cast<std::int64_t>(L)))));
    const Expr F = substituteBack(c, r.F, t, root);
    // Gate: structural round-trip. The x-derivative necessarily
    // carries the fractional Jacobian x^(1/L - 1), so no polynomial
    // gate exists in one coordinate; the t-identity d/dt r.F = G is
    // the kernel's own certificate, the Jacobian was attached
    // exactly, and rebuilding F with the SAME L must return r.F.
    if (radicalRebuild(c, F, var, t, L) != r.F) {
        out.reason = "radical substitution certificate failed";
        return out;
    }
    out.F = F;
    out.status = RationalIntegral::Status::ProvedSymbolic;
    return out;
}

static RationalIntegral integrateTanRational(Ctx &c, Expr f, Expr var,
                                             Budget *budget)
{
    RationalIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    const Expr t = c.symbol("#t");
    bool ok = true;
    const Expr g = substituteTangent(c, f, var, t, ok);
    if (!ok) {
        out.reason = "integrand is not rational in sin/cos of the variable";
        return out;
    }
    // Jacobian dx = 2 dt / (1 + t^2).
    const Expr t2p1 =
        c.add({c.one(), c.pow(t, c.number(std::int64_t{2}))});
    const RationalIntegral r = integrateRational(
        c, c.div(c.mul({c.number(std::int64_t{2}), g}), t2p1), t, budget);
    if (!r.proved()) {
        out.reason = (budget && !budget->ok()) ? r.reason
                                               : "tan substitution: " + r.reason;
        return out;
    }
    const Expr halfTan = c.func("tan", halfArg(c, var));
    const Expr F = substituteBack(c, r.F, t, halfTan);
    // Primary gate: rationalize dF/dx in the t-world and compare
    // polynomials against the substituted integrand times the
    // Jacobian; fallback: the structural round-trip.
    const Expr dFT = substituteTangent(c, c.diff(F, var), var, t, ok);
    UPoly n1, d1, n2, d2;
    const bool polyGate =
        ok && toRational(c, dFT, t, n1, d1) && toRational(c, g, t, n2, d2) &&
        n1 == n2 && d1 == d2;
    if (!polyGate) {
        bool ok2 = true;
        if (substituteTangent(c, F, var, t, ok2) != r.F || !ok2) {
            out.reason = "tan substitution certificate failed";
            return out;
        }
    }
    out.F = F;
    out.status = RationalIntegral::Status::ProvedSymbolic;
    return out;
}

RationalIntegral integrateRational(Ctx &c, Expr f, Expr var, Budget *budget)
{
    RationalIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    UPoly N, D;
    if (!toRational(c, f, var, N, D)) {
        // Substitution storeys must only fire on integrands that
        // actually depend on the variable: a foreign-symbol constant
        // (say 1/y) would otherwise ping-pong exp->log->exp through
        // fresh substitution symbols forever (f*t cancels the symbol
        // again) until the stack dies.
        if (!mentionsVar(c, f, var)) {
            out.reason = "integrand does not depend on the variable";
            return out;
        }
        RationalIntegral r = integrateExpRational(c, f, var, budget);
        if (r.proved() || (budget && !budget->ok()))
            return r;
        std::string why = r.reason;
        r = integrateLogRational(c, f, var, budget);
        if (r.proved() || (budget && !budget->ok()))
            return r;
        why += "; " + r.reason;
        r = integrateTanRational(c, f, var, budget);
        if (r.proved() || (budget && !budget->ok()))
            return r;
        why += "; " + r.reason;
        r = integrateRadicalRational(c, f, var, budget);
        if (r.proved() || (budget && !budget->ok()))
            return r;
        r.reason = why + "; " + r.reason;
        return r;
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
    if (!checkBudget(c, budget, out.reason))
        return out;

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
                                 qcertN, qcertD, out.reason, budget))
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

    // Tier-2a certified interval audit of the FORM (plan D-series).
    // The Tier-1 certificate above proves the SUM OF PIECE
    // DERIVATIVES equals the integrand in Q(x); the extraTerms
    // (RootOf/Rioboo emissions, transcendental storeys) are NOT in
    // that loop, so the printed form itself is audited here:
    // diff(F) and the integrand compared as exact rational
    // enclosures at sample points (RootOf via isolating intervals).
    // A disjoint pair is CERTIFIED form error -> honest Unevaluated;
    // transcendental inputs are Unknown and pass (their storeys
    // carry their own gates).
    if (tier2aFormCheck(c, out.F, f, var) == Tier2aStatus::Mismatch) {
        out.F = Expr();
        out.status = RationalIntegral::Status::Unevaluated;
        out.reason = "internal interval form check failed";
        return out;
    }

    out.status = RationalIntegral::Status::ProvedSymbolic;
    out.reason.clear();
    return out;
}

namespace {

bool extractPolyInVar(Ctx &c, Expr e, Expr var, int maxDeg,
                      std::vector<Expr> &coeffsOut)
{
    if (e.isNull() || maxDeg < 0)
        return false;
    const Expr ex = c.expand(e);
    if (!mentionsVar(c, ex, var)) {
        coeffsOut.clear();
        if (!c.isZero(ex))
            coeffsOut.push_back(ex);
        return true;
    }

    auto matchMonomial = [&](Expr term, int &degOut, Expr &cfOut) -> bool {
        if (!mentionsVar(c, term, var)) {
            degOut = 0;
            cfOut = term;
            return true;
        }
        if (term == var) {
            degOut = 1;
            cfOut = c.one();
            return true;
        }
        if (c.kind(term) == NodeKind::Pow && c.child(term, 0) == var &&
            c.kind(c.child(term, 1)) == NodeKind::Number) {
            const Rational &re = c.numberValue(c.child(term, 1));
            std::int64_t d = 0;
            if (re.den() == BigInt(1) && re.num().fitsInt64(d) && d >= 1 &&
                d <= maxDeg) {
                degOut = static_cast<int>(d);
                cfOut = c.one();
                return true;
            }
            return false;
        }
        if (c.kind(term) == NodeKind::Mul) {
            std::vector<Expr> others;
            int deg = 0;
            for (std::size_t i = 0; i < c.childCount(term); ++i) {
                const Expr ch = c.child(term, i);
                if (ch == var) {
                    deg += 1;
                } else if (c.kind(ch) == NodeKind::Pow &&
                           c.child(ch, 0) == var &&
                           c.kind(c.child(ch, 1)) == NodeKind::Number) {
                    const Rational &re = c.numberValue(c.child(ch, 1));
                    std::int64_t d = 0;
                    if (re.den() == BigInt(1) && re.num().fitsInt64(d) &&
                        d >= 1 && d <= maxDeg) {
                        deg += static_cast<int>(d);
                    } else {
                        return false;
                    }
                } else if (!mentionsVar(c, ch, var)) {
                    others.push_back(ch);
                } else {
                    return false;
                }
            }
            if (deg >= 0 && deg <= maxDeg) {
                degOut = deg;
                cfOut = others.empty() ? c.one() : c.mul(others);
                return true;
            }
        }
        return false;
    };

    std::vector<std::vector<Expr>> buckets(static_cast<std::size_t>(maxDeg + 1));
    if (c.kind(ex) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(ex); ++i) {
            int d = 0;
            Expr cf;
            if (!matchMonomial(c.child(ex, i), d, cf))
                return false;
            buckets[static_cast<std::size_t>(d)].push_back(cf);
        }
    } else {
        int d = 0;
        Expr cf;
        if (!matchMonomial(ex, d, cf))
            return false;
        buckets[static_cast<std::size_t>(d)].push_back(cf);
    }

    coeffsOut.assign(static_cast<std::size_t>(maxDeg + 1), c.zero());
    for (int d = 0; d <= maxDeg; ++d) {
        const auto &b = buckets[static_cast<std::size_t>(d)];
        if (!b.empty())
            coeffsOut[static_cast<std::size_t>(d)] =
                b.size() == 1 ? b[0] : c.simplify(c.add(b));
    }
    while (!coeffsOut.empty() && c.isZero(coeffsOut.back()))
        coeffsOut.pop_back();
    return true;
}

Expr evalSymbolicPoly(Ctx &c, const std::vector<Expr> &coeffs, Expr var)
{
    std::vector<Expr> terms;
    for (std::size_t d = 0; d < coeffs.size(); ++d) {
        if (c.isZero(coeffs[d]))
            continue;
        if (d == 0) {
            terms.push_back(coeffs[d]);
        } else if (d == 1) {
            terms.push_back(c.mul({coeffs[d], var}));
        } else {
            terms.push_back(c.mul(
                {coeffs[d], c.pow(var, c.number(static_cast<std::int64_t>(d)))}));
        }
    }
    return terms.empty() ? c.zero() : c.add(terms);
}

bool isNegativeSymbolicFactor(const Ctx &c, Expr a)
{
    if (a.isNull())
        return false;
    if (c.isAssumedNegative(a))
        return true;
    if (c.kind(a) == NodeKind::Number)
        return c.numberValue(a).signum() < 0;
    if (c.kind(a) == NodeKind::Mul && c.childCount(a) > 0 &&
        c.kind(c.child(a, 0)) == NodeKind::Number) {
        return c.numberValue(c.child(a, 0)).signum() < 0;
    }
    return false;
}

// Compute sqrt(expr) and 1/sqrt(expr) factor-by-factor across a product so that
// c.mul({sqrtOut, invSqrtOut}) == 1 and c.pow(sqrtOut, 2) == expr in Ctx.
void sqrtFactorPair(Ctx &c, Expr expr, Expr &sqrtOut, Expr &invSqrtOut)
{
    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
    const Expr negHalf = c.number(Rational(std::int64_t{-1}, BigInt(2)));
    auto single = [&](Expr f, Expr &s, Expr &invS) {
        if (c.kind(f) == NodeKind::Number && c.numberValue(f).signum() > 0) {
            const Rational &r = c.numberValue(f);
            BigInt rn, rd;
            if (r.num().sqrtExact(rn) && r.den().sqrtExact(rd)) {
                s = c.number(Rational(rn, rd));
                invS = c.number(Rational(rd, rn));
                return;
            }
        }
        if (c.kind(f) == NodeKind::Pow &&
            c.kind(c.child(f, 1)) == NodeKind::Number) {
            const Expr base = c.child(f, 0);
            const Rational halfExp =
                c.numberValue(c.child(f, 1)) * Rational(std::int64_t{1}, BigInt(2));
            s = c.pow(base, c.number(halfExp));
            invS = c.pow(base, c.number(-halfExp));
            return;
        }
        s = c.pow(f, half);
        invS = c.pow(f, negHalf);
    };
    if (c.kind(expr) == NodeKind::Mul) {
        std::vector<Expr> sFactors, invFactors;
        for (std::size_t i = 0; i < c.childCount(expr); ++i) {
            Expr si, isi;
            single(c.child(expr, i), si, isi);
            sFactors.push_back(si);
            invFactors.push_back(isi);
        }
        sqrtOut = c.mul(sFactors);
        invSqrtOut = c.mul(invFactors);
        return;
    }
    single(expr, sqrtOut, invSqrtOut);
}

Expr expandFuncArgs(Ctx &c, Expr e)
{
    if (e.isNull())
        return Expr();
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        std::vector<Expr> args;
        args.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            args.push_back(c.expand(expandFuncArgs(c, c.child(e, i))));
        return c.func(c.funcName(e), args);
    }
    case NodeKind::Pow:
        return c.pow(expandFuncArgs(c, c.child(e, 0)),
                     expandFuncArgs(c, c.child(e, 1)));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            ch.push_back(expandFuncArgs(c, c.child(e, i)));
        return c.kind(e) == NodeKind::Add ? c.add(ch) : c.mul(ch);
    }
    }
    return e;
}

bool certifySpecialIntegral(Ctx &c, Expr F, Expr f, Expr var)
{
    if (F.isNull() || f.isNull())
        return false;
    const Expr diffRaw = c.add({c.diff(F, var), c.neg(f)});
    if (c.isZero(diffRaw))
        return true;
    const Expr diffSimp = c.simplify(diffRaw);
    if (!diffSimp.isNull() && c.isZero(diffSimp))
        return true;
    const Expr diffExp = c.simplify(c.expand(expandFuncArgs(c, diffRaw)));
    return !diffExp.isNull() && c.isZero(diffExp);
}

bool integrateLinearLogOverLinearPole(Ctx &c, Expr logArg, Expr a, Expr b,
                                      Expr linBase, Expr c1, Expr c0,
                                      std::int64_t poleK, Expr numExpr,
                                      Expr var, Budget *budget, Expr &fOut)
{
    const Expr lSym = c.symbol("_L_dilog");
    const Expr varInL = c.div(c.add({lSym, c.neg(c0)}), c1);
    std::vector<Expr> lPoly;
    if (!extractPolyInVar(c, c.subs(numExpr, var, varInL), lSym, 8, lPoly))
        return false;

    const Expr invC1 = c.pow(c1, c.number(std::int64_t{-1}));
    const Expr W =
        c.simplify(c.add({c.mul({a, c0}), c.neg(c.mul({b, c1}))}));
    Expr baseI1;
    if (c.isZero(W)) {
        baseI1 = c.mul({c.number(Rational(std::int64_t{1}, BigInt(2))), invC1,
                        c.pow(c.func("log", logArg), c.number(std::int64_t{2}))});
    } else if (c.isZero(c.simplify(c.add({W, c1})))) {
        const Expr u = c.simplify(c.add({c.one(), c.neg(logArg)}));
        baseI1 = c.neg(c.mul({invC1, c.func("dilog", u)}));
    } else {
        const Expr w = c.simplify(c.neg(c.div(c.mul({c1, logArg}), W)));
        const Expr oneMinusW = c.simplify(c.add({c.one(), c.neg(w)}));
        baseI1 = c.mul(
            {invC1,
             c.add({c.mul({c.func("log", logArg), c.func("log", oneMinusW)}),
                    c.func("dilog", w)})});
    }

    std::vector<Expr> pieces;
    for (std::size_t j = 0; j < lPoly.size(); ++j) {
        if (c.isZero(lPoly[j]))
            continue;
        const std::int64_t m = poleK - static_cast<std::int64_t>(j);
        if (m == 1) {
            pieces.push_back(c.mul({lPoly[j], baseI1}));
        } else if (m >= 2) {
            const Expr denom = c.mul({c1, c.number(m - 1)});
            const Expr lPow = c.pow(linBase, c.number(-(m - 1)));
            const Expr ibpBoundary =
                c.neg(c.div(c.mul({c.func("log", logArg), lPow}), denom));
            const Expr ratIntegrand =
                c.mul({c.div(a, denom),
                       c.pow(logArg, c.number(std::int64_t{-1})), lPow});
            const RationalIntegral ratInt =
                integrate(c, ratIntegrand, var, budget);
            if (!ratInt.proved())
                return false;
            pieces.push_back(
                c.mul({lPoly[j], c.add({ibpBoundary, ratInt.F})}));
        } else {
            const Expr elemIntegrand =
                c.mul({lPoly[j], c.pow(linBase, c.number(-m)),
                       c.func("log", logArg)});
            const RationalIntegral elemInt =
                integrate(c, elemIntegrand, var, budget);
            if (!elemInt.proved())
                return false;
            pieces.push_back(elemInt.F);
        }
    }
    fOut = pieces.empty() ? c.zero() : c.add(pieces);
    return true;
}

RationalIntegral integrateSpecialFunctions(Ctx &c, Expr f, Expr var,
                                           Budget *budget)
{
    RationalIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;

    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));

    // Collect top-level multiplicative factors of `f`.
    std::vector<Expr> factors;
    if (c.kind(f) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(f); ++i)
            factors.push_back(c.child(f, i));
    } else {
        factors.push_back(f);
    }

    // 1. Check for exp(...) factor (Gaussian erf/erfi or Exponential Integral Ei).
    std::vector<Expr> expArgs;
    std::vector<Expr> nonExpFactors;
    for (const Expr &fac : factors) {
        if (c.kind(fac) == NodeKind::Func && c.funcName(fac) == "exp") {
            expArgs.push_back(c.child(fac, 0));
        } else if (c.kind(fac) == NodeKind::Pow &&
                   c.kind(c.child(fac, 0)) == NodeKind::Func &&
                   c.funcName(c.child(fac, 0)) == "exp") {
            expArgs.push_back(c.mul({c.child(fac, 1), c.child(c.child(fac, 0), 0)}));
        } else {
            nonExpFactors.push_back(fac);
        }
    }
    if (!expArgs.empty()) {
        const Expr qExpr =
            expArgs.size() == 1 ? expArgs[0] : c.add(expArgs);
        const Expr rest =
            nonExpFactors.empty() ? c.one() : c.mul(nonExpFactors);
        std::vector<Expr> qCoeffs;
        if (extractPolyInVar(c, qExpr, var, 2, qCoeffs)) {
            // 1a. Gaussian integral: int P(x) * exp(a*x^2 + b*x + d) dx.
            std::vector<Expr> pCoeffs;
            if (qCoeffs.size() == 3 && !c.isZero(qCoeffs[2]) &&
                extractPolyInVar(c, rest, var, 12, pCoeffs) &&
                !pCoeffs.empty()) {
                const Expr d = qCoeffs[0];
                const Expr b = qCoeffs[1];
                const Expr a = qCoeffs[2];
                const Expr twoA = c.mul({c.number(std::int64_t{2}), a});
                std::vector<Expr> qPoly(
                    pCoeffs.size() >= 2 ? pCoeffs.size() - 1 : 0, c.zero());
                for (int m = static_cast<int>(pCoeffs.size()) - 1; m >= 1; --m) {
                    const Expr pm = pCoeffs[static_cast<std::size_t>(m)];
                    if (c.isZero(pm))
                        continue;
                    const Expr cm1 = c.simplify(c.div(pm, twoA));
                    qPoly[static_cast<std::size_t>(m - 1)] = cm1;
                    pCoeffs[static_cast<std::size_t>(m - 1)] = c.simplify(c.add(
                        {pCoeffs[static_cast<std::size_t>(m - 1)],
                         c.neg(c.mul({b, cm1}))}));
                    if (m >= 2) {
                        pCoeffs[static_cast<std::size_t>(m - 2)] =
                            c.simplify(c.add(
                                {pCoeffs[static_cast<std::size_t>(m - 2)],
                                 c.neg(c.mul(
                                     {c.number(static_cast<std::int64_t>(m - 1)),
                                      cm1}))}));
                    }
                }
                const Expr p0 = pCoeffs[0];
                const Expr elemPart = c.mul(
                    {evalSymbolicPoly(c, qPoly, var), c.func("exp", qExpr)});
                const bool useErf = isNegativeSymbolicFactor(c, a);
                const Expr alpha = useErf ? c.neg(a) : a;
                Expr sqrtAlpha, invSqrtAlpha;
                sqrtFactorPair(c, alpha, sqrtAlpha, invSqrtAlpha);
                const Expr shift =
                    c.isZero(b) ? var : c.add({var, c.div(b, twoA)});
                const Expr constExp = c.simplify(c.add(
                    {d, c.neg(c.div(c.pow(b, c.number(std::int64_t{2})),
                                    c.mul({c.number(std::int64_t{4}), a})))}));
                const Expr u = c.mul({sqrtAlpha, shift});
                const Expr erfPart = c.mul(
                    {p0, half, c.pow(c.symbol("pi"), half), invSqrtAlpha,
                     c.func("exp", constExp),
                     c.func(useErf ? "erf" : "erfi", u)});
                const Expr F = c.add({elemPart, erfPart});
                if (certifySpecialIntegral(c, F, f, var)) {
                    out.F = F;
                    out.status = RationalIntegral::Status::ProvedSymbolic;
                    return out;
                }
            }

            // 1b. Exponential integral: int P(x) * exp(a*x + b) / (c1*x + c0)^k dx.
            if (qCoeffs.size() == 2 && !c.isZero(qCoeffs[1])) {
                const Expr b = qCoeffs[0];
                const Expr a = qCoeffs[1];
                std::vector<Expr> numFacs;
                Expr linBase;
                std::int64_t poleK = 0;
                for (const Expr &rf : nonExpFactors) {
                    if (poleK == 0 && c.kind(rf) == NodeKind::Pow &&
                        c.kind(c.child(rf, 1)) == NodeKind::Number) {
                        const Rational &re = c.numberValue(c.child(rf, 1));
                        std::int64_t kVal = 0;
                        std::vector<Expr> lCoeffs;
                        if (re.den() == BigInt(1) && re.num().fitsInt64(kVal) &&
                            kVal <= -1 && kVal >= -6 &&
                            extractPolyInVar(c, c.child(rf, 0), var, 1, lCoeffs) &&
                            lCoeffs.size() == 2 && !c.isZero(lCoeffs[1])) {
                            linBase = c.child(rf, 0);
                            poleK = -kVal;
                            continue;
                        }
                    }
                    numFacs.push_back(rf);
                }
                if (poleK >= 1) {
                    std::vector<Expr> lCoeffs;
                    extractPolyInVar(c, linBase, var, 1, lCoeffs);
                    const Expr c0 = lCoeffs[0];
                    const Expr c1 = lCoeffs[1];
                    const Expr numExpr =
                        numFacs.empty() ? c.one() : c.mul(numFacs);
                    // Rewrite numExpr in powers of L = c1*var + c0 via var = (L - c0)/c1.
                    const Expr lSym = c.symbol("_L_ei");
                    const Expr varInL =
                        c.div(c.add({lSym, c.neg(c0)}), c1);
                    std::vector<Expr> lPoly;
                    if (extractPolyInVar(c, c.subs(numExpr, var, varInL), lSym,
                                         8, lPoly)) {
                        std::vector<Expr> fPieces;
                        bool okPieces = true;
                        // Precompute I_m = int exp(a*x+b) / L^m dx for m = 1..poleK.
                        std::vector<Expr> iPow(static_cast<std::size_t>(poleK + 1));
                        const Expr shiftExp = c.simplify(
                            c.add({b, c.neg(c.div(c.mul({a, c0}), c1))}));
                        const Expr uEi = c.mul({c.div(a, c1), linBase});
                        iPow[1] = c.mul({c.pow(c1, c.number(std::int64_t{-1})),
                                         c.func("exp", shiftExp),
                                         c.func("Ei", uEi)});
                        for (std::int64_t m = 2; m <= poleK; ++m) {
                            const Expr denom = c.mul(
                                {c1, c.number(m - 1)});
                            const Expr boundary = c.neg(c.div(
                                c.mul({c.func("exp", qExpr),
                                       c.pow(linBase, c.number(-(m - 1)))}),
                                denom));
                            const Expr rec =
                                c.mul({c.div(a, denom),
                                       iPow[static_cast<std::size_t>(m - 1)]});
                            iPow[static_cast<std::size_t>(m)] =
                                c.add({boundary, rec});
                        }
                        for (std::size_t j = 0; j < lPoly.size(); ++j) {
                            if (c.isZero(lPoly[j]))
                                continue;
                            const std::int64_t m =
                                poleK - static_cast<std::int64_t>(j);
                            if (m >= 1) {
                                fPieces.push_back(c.mul(
                                    {lPoly[j],
                                     iPow[static_cast<std::size_t>(m)]}));
                            } else {
                                const Expr elemIntegrand = c.mul(
                                    {lPoly[j], c.pow(linBase, c.number(-m)),
                                     c.func("exp", qExpr)});
                                const RationalIntegral elemInt =
                                    integrate(c, elemIntegrand, var, budget);
                                if (!elemInt.proved()) {
                                    okPieces = false;
                                    break;
                                }
                                fPieces.push_back(elemInt.F);
                            }
                        }
                        if (okPieces) {
                            const Expr F =
                                fPieces.empty() ? c.zero() : c.add(fPieces);
                            if (certifySpecialIntegral(c, F, f, var)) {
                                out.F = F;
                                out.status =
                                    RationalIntegral::Status::ProvedSymbolic;
                                return out;
                            }
                        }
                    }
                }

                // 1c. Incomplete gamma integral:
                //     int C * x^(s - 1) * exp(a*x + b) dx = -C * exp(b) * (-a)^(-s) * igamma(s, -a*x)
                {
                    Expr xExp = c.zero();
                    std::vector<Expr> cFacs;
                    bool okMonom = true;
                    for (const Expr &rf : nonExpFactors) {
                        if (!mentionsVar(c, rf, var)) {
                            cFacs.push_back(rf);
                        } else if (rf == var) {
                            xExp = c.add({xExp, c.one()});
                        } else if (c.kind(rf) == NodeKind::Pow &&
                                   c.child(rf, 0) == var &&
                                   !mentionsVar(c, c.child(rf, 1), var)) {
                            xExp = c.add({xExp, c.child(rf, 1)});
                        } else {
                            okMonom = false;
                            break;
                        }
                    }
                    const Expr sParam = c.simplify(c.add({xExp, c.one()}));
                    if (okMonom && !c.isZero(xExp) && !c.isZero(sParam)) {
                        const Expr negA = c.simplify(c.neg(a));
                        const Expr cPart =
                            cFacs.empty() ? c.one() : c.mul(cFacs);
                        const Expr expB =
                            c.isZero(b) ? c.one() : c.func("exp", b);
                        const Expr uGam = c.mul({negA, var});
                        // Use (-a)^(-s) when -a > 0; otherwise x^s * (-a*x)^(-s)
                        Expr scalePow;
                        if ((c.kind(negA) == NodeKind::Number &&
                             c.numberValue(negA) > Rational(0)) ||
                            c.isAssumedPositive(negA)) {
                            scalePow = c.pow(negA, c.neg(sParam));
                        } else {
                            scalePow = c.mul({
                                c.pow(var, sParam),
                                c.pow(uGam, c.neg(sParam))});
                        }
                        const Expr F = c.neg(c.mul({
                            cPart, expB, scalePow,
                            c.func("igamma", sParam, uGam)}));
                        if (certifySpecialIntegral(c, F, f, var)) {
                            out.F = F;
                            out.status =
                                RationalIntegral::Status::ProvedSymbolic;
                            return out;
                        }
                    }
                }
            }
        }
    }

    // 2. Logarithmic integral: int (a*x + b)^m / log(a*x + b) dx.
    {
        Expr logArg;
        std::vector<Expr> restFacs;
        for (const Expr &fac : factors) {
            if (logArg.isNull() && c.kind(fac) == NodeKind::Pow &&
                c.child(fac, 1) == c.number(std::int64_t{-1}) &&
                c.kind(c.child(fac, 0)) == NodeKind::Func &&
                c.funcName(c.child(fac, 0)) == "log") {
                logArg = c.child(c.child(fac, 0), 0);
            } else {
                restFacs.push_back(fac);
            }
        }
        std::vector<Expr> lCoeffs;
        if (!logArg.isNull() && extractPolyInVar(c, logArg, var, 1, lCoeffs) &&
            lCoeffs.size() == 2 && !c.isZero(lCoeffs[1])) {
            const Expr a = lCoeffs[1];
            const Expr rest =
                restFacs.empty() ? c.one() : c.mul(restFacs);
            if (!mentionsVar(c, rest, var)) {
                const Expr F = c.mul(
                    {rest, c.pow(a, c.number(std::int64_t{-1})),
                     c.func("li", logArg)});
                if (certifySpecialIntegral(c, F, f, var)) {
                    out.F = F;
                    out.status = RationalIntegral::Status::ProvedSymbolic;
                    return out;
                }
            }
            // Check if rest == const * logArg^m (m != -1).
            const Expr lSym = c.symbol("_L_li");
            const Expr varInL = c.div(c.add({lSym, c.neg(lCoeffs[0])}), a);
            const Expr restInL = c.simplify(c.subs(rest, var, varInL));
            std::vector<Expr> mPoly;
            if (extractPolyInVar(c, restInL, lSym, 8, mPoly)) {
                std::vector<Expr> pieces;
                for (std::size_t m = 0; m < mPoly.size(); ++m) {
                    if (c.isZero(mPoly[m]))
                        continue;
                    if (m == 0) {
                        pieces.push_back(
                            c.mul({mPoly[0], c.pow(a, c.number(std::int64_t{-1})),
                                   c.func("li", logArg)}));
                    } else {
                        const Expr mPlus1 =
                            c.number(static_cast<std::int64_t>(m + 1));
                        pieces.push_back(c.mul(
                            {mPoly[m], c.pow(a, c.number(std::int64_t{-1})),
                             c.func("Ei",
                                    c.mul({mPlus1, c.func("log", logArg)}))}));
                    }
                }
                const Expr F = pieces.empty() ? c.zero() : c.add(pieces);
                if (certifySpecialIntegral(c, F, f, var)) {
                    out.F = F;
                    out.status = RationalIntegral::Status::ProvedSymbolic;
                    return out;
                }
            }
        }
    }

    // 3. Sine/Cosine integrals (Si, Ci) and Fresnel integrals (FresnelS, FresnelC).
    {
        std::string trigFn;
        Expr trigArg;
        std::vector<Expr> nonTrigFacs;
        for (const Expr &fac : factors) {
            if (trigFn.empty() && c.kind(fac) == NodeKind::Func &&
                (c.funcName(fac) == "sin" || c.funcName(fac) == "cos")) {
                trigFn = c.funcName(fac);
                trigArg = c.child(fac, 0);
            } else {
                nonTrigFacs.push_back(fac);
            }
        }
        std::vector<Expr> tCoeffs;
        if (!trigFn.empty() && extractPolyInVar(c, trigArg, var, 2, tCoeffs)) {
            const Expr rest =
                nonTrigFacs.empty() ? c.one() : c.mul(nonTrigFacs);

            // 3a. Sine / Cosine integral: sin(a*x + b) / (c1*x + c0)^k or cos(a*x + b) / (c1*x + c0)^k.
            if (tCoeffs.size() == 2 && !c.isZero(tCoeffs[1])) {
                const Expr b = tCoeffs[0];
                const Expr a = tCoeffs[1];
                std::vector<Expr> numFacs;
                Expr linBase;
                std::int64_t poleK = 0;
                for (const Expr &rf : nonTrigFacs) {
                    if (poleK == 0 && c.kind(rf) == NodeKind::Pow &&
                        c.kind(c.child(rf, 1)) == NodeKind::Number) {
                        const Rational &re = c.numberValue(c.child(rf, 1));
                        std::int64_t kVal = 0;
                        std::vector<Expr> lCoeffs;
                        if (re.den() == BigInt(1) && re.num().fitsInt64(kVal) &&
                            kVal <= -1 && kVal >= -4 &&
                            extractPolyInVar(c, c.child(rf, 0), var, 1, lCoeffs) &&
                            lCoeffs.size() == 2 && !c.isZero(lCoeffs[1])) {
                            linBase = c.child(rf, 0);
                            poleK = -kVal;
                            continue;
                        }
                    }
                    numFacs.push_back(rf);
                }
                if (poleK >= 1) {
                    std::vector<Expr> lCoeffs;
                    extractPolyInVar(c, linBase, var, 1, lCoeffs);
                    const Expr c0 = lCoeffs[0];
                    const Expr c1 = lCoeffs[1];
                    const Expr numExpr =
                        numFacs.empty() ? c.one() : c.mul(numFacs);
                    const Expr lSym = c.symbol("_L_si");
                    const Expr varInL = c.div(c.add({lSym, c.neg(c0)}), c1);
                    std::vector<Expr> lPoly;
                    if (extractPolyInVar(c, c.subs(numExpr, var, varInL), lSym,
                                         6, lPoly)) {
                        const Expr phi = c.simplify(
                            c.add({b, c.neg(c.div(c.mul({a, c0}), c1))}));
                        const Expr uSi = c.isZero(phi)
                                             ? trigArg
                                             : c.mul({c.div(a, c1), linBase});
                        const Expr invC1 = c.pow(c1, c.number(std::int64_t{-1}));
                        std::vector<Expr> sinInt(
                            static_cast<std::size_t>(poleK + 1));
                        std::vector<Expr> cosInt(
                            static_cast<std::size_t>(poleK + 1));
                        if (c.isZero(phi)) {
                            sinInt[1] = c.mul({invC1, c.func("Si", uSi)});
                            cosInt[1] = c.mul({invC1, c.func("Ci", uSi)});
                        } else {
                            const Expr cosPhi = c.simplify(c.func("cos", phi));
                            const Expr sinPhi = c.simplify(c.func("sin", phi));
                            sinInt[1] = c.mul(
                                {invC1,
                                 c.add({c.mul({cosPhi, c.func("Si", uSi)}),
                                        c.mul({sinPhi, c.func("Ci", uSi)})})});
                            cosInt[1] = c.mul(
                                {invC1,
                                 c.add({c.mul({cosPhi, c.func("Ci", uSi)}),
                                        c.neg(c.mul(
                                            {sinPhi, c.func("Si", uSi)}))})});
                        }
                        for (std::int64_t m = 2; m <= poleK; ++m) {
                            const Expr denom = c.mul({c1, c.number(m - 1)});
                            const Expr lPow =
                                c.pow(linBase, c.number(-(m - 1)));
                            sinInt[static_cast<std::size_t>(m)] = c.add(
                                {c.neg(c.div(
                                     c.mul({c.func("sin", trigArg), lPow}),
                                     denom)),
                                 c.mul({c.div(a, denom),
                                        cosInt[static_cast<std::size_t>(m - 1)]})});
                            cosInt[static_cast<std::size_t>(m)] = c.add(
                                {c.neg(c.div(
                                     c.mul({c.func("cos", trigArg), lPow}),
                                     denom)),
                                 c.neg(c.mul(
                                     {c.div(a, denom),
                                      sinInt[static_cast<std::size_t>(m - 1)]}))});
                        }
                        std::vector<Expr> fPieces;
                        bool okPieces = true;
                        for (std::size_t j = 0; j < lPoly.size(); ++j) {
                            if (c.isZero(lPoly[j]))
                                continue;
                            const std::int64_t m =
                                poleK - static_cast<std::int64_t>(j);
                            if (m >= 1) {
                                const Expr baseInt =
                                    (trigFn == "sin")
                                        ? sinInt[static_cast<std::size_t>(m)]
                                        : cosInt[static_cast<std::size_t>(m)];
                                fPieces.push_back(c.mul({lPoly[j], baseInt}));
                            } else {
                                const Expr elemIntegrand =
                                    c.mul({lPoly[j], c.pow(linBase, c.number(-m)),
                                           c.func(trigFn, trigArg)});
                                const RationalIntegral elemInt =
                                    integrate(c, elemIntegrand, var, budget);
                                if (!elemInt.proved()) {
                                    okPieces = false;
                                    break;
                                }
                                fPieces.push_back(elemInt.F);
                            }
                        }
                        if (okPieces) {
                            const Expr F =
                                fPieces.empty() ? c.zero() : c.add(fPieces);
                            if (certifySpecialIntegral(c, F, f, var)) {
                                out.F = c.simplify(F);
                                out.status =
                                    RationalIntegral::Status::ProvedSymbolic;
                                return out;
                            }
                        }
                    }
                }
            }

            // 3b. Fresnel integrals: int P(x) * sin(a*x^2 + b*x + d) dx and cos.
            std::vector<Expr> pCoeffs;
            if (tCoeffs.size() == 3 && !c.isZero(tCoeffs[2]) &&
                extractPolyInVar(c, rest, var, 8, pCoeffs) &&
                !pCoeffs.empty()) {
                const Expr d = tCoeffs[0];
                const Expr b = tCoeffs[1];
                const Expr a = tCoeffs[2];
                const Expr twoA = c.mul({c.number(std::int64_t{2}), a});
                const std::size_t degP = pCoeffs.size();
                std::vector<Expr> sPoly(degP, c.zero());
                std::vector<Expr> cPoly(degP, c.zero());
                if (trigFn == "sin")
                    sPoly = pCoeffs;
                else
                    cPoly = pCoeffs;

                std::vector<Expr> elemSin(degP >= 2 ? degP - 1 : 0, c.zero());
                std::vector<Expr> elemCos(degP >= 2 ? degP - 1 : 0, c.zero());
                for (int m = static_cast<int>(degP) - 1; m >= 1; --m) {
                    const Expr sm = sPoly[static_cast<std::size_t>(m)];
                    if (!c.isZero(sm)) {
                        const Expr k = c.simplify(c.div(sm, twoA));
                        elemCos[static_cast<std::size_t>(m - 1)] = c.simplify(
                            c.add({elemCos[static_cast<std::size_t>(m - 1)],
                                   c.neg(k)}));
                        sPoly[static_cast<std::size_t>(m - 1)] = c.simplify(
                            c.add({sPoly[static_cast<std::size_t>(m - 1)],
                                   c.neg(c.mul({b, k}))}));
                        if (m >= 2) {
                            cPoly[static_cast<std::size_t>(m - 2)] = c.simplify(
                                c.add({cPoly[static_cast<std::size_t>(m - 2)],
                                       c.mul({c.number(
                                                  static_cast<std::int64_t>(m - 1)),
                                              k})}));
                        }
                    }
                    const Expr cm = cPoly[static_cast<std::size_t>(m)];
                    if (!c.isZero(cm)) {
                        const Expr k = c.simplify(c.div(cm, twoA));
                        elemSin[static_cast<std::size_t>(m - 1)] = c.simplify(
                            c.add({elemSin[static_cast<std::size_t>(m - 1)], k}));
                        cPoly[static_cast<std::size_t>(m - 1)] = c.simplify(
                            c.add({cPoly[static_cast<std::size_t>(m - 1)],
                                   c.neg(c.mul({b, k}))}));
                        if (m >= 2) {
                            sPoly[static_cast<std::size_t>(m - 2)] = c.simplify(
                                c.add({sPoly[static_cast<std::size_t>(m - 2)],
                                       c.neg(c.mul(
                                           {c.number(
                                                static_cast<std::int64_t>(m - 1)),
                                            k}))}));
                        }
                    }
                }

                const Expr elemPart = c.add(
                    {c.mul({evalSymbolicPoly(c, elemSin, var),
                            c.func("sin", trigArg)}),
                     c.mul({evalSymbolicPoly(c, elemCos, var),
                            c.func("cos", trigArg)})});
                const bool negA = isNegativeSymbolicFactor(c, a);
                const Expr alpha = negA ? c.neg(a) : a;
                const Expr twoAlphaOverPi = c.mul(
                    {c.number(std::int64_t{2}), alpha,
                     c.pow(c.symbol("pi"), c.number(std::int64_t{-1}))});
                Expr scale, invScale;
                sqrtFactorPair(c, twoAlphaOverPi, scale, invScale);
                const Expr shift =
                    c.isZero(b) ? var : c.add({var, c.div(b, twoA)});
                const Expr phi = c.simplify(c.add(
                    {d, c.neg(c.div(c.pow(b, c.number(std::int64_t{2})),
                                    c.mul({c.number(std::int64_t{4}), a})))}));
                const Expr u = c.mul({scale, shift});
                const Expr baseS =
                    c.mul({invScale, c.func("FresnelS", u),
                           c.number(negA ? std::int64_t{-1} : std::int64_t{1})});
                const Expr baseC = c.mul({invScale, c.func("FresnelC", u)});

                Expr intSinQ, intCosQ;
                if (c.isZero(phi)) {
                    intSinQ = baseS;
                    intCosQ = baseC;
                } else {
                    const Expr cosPhi = c.simplify(c.func("cos", phi));
                    const Expr sinPhi = c.simplify(c.func("sin", phi));
                    intSinQ = c.add(
                        {c.mul({cosPhi, baseS}), c.mul({sinPhi, baseC})});
                    intCosQ = c.add(
                        {c.mul({cosPhi, baseC}), c.neg(c.mul({sinPhi, baseS}))});
                }
                const Expr F = c.add({elemPart, c.mul({sPoly[0], intSinQ}),
                                      c.mul({cPoly[0], intCosQ})});
                if (certifySpecialIntegral(c, F, f, var)) {
                    out.F = F;
                    out.status = RationalIntegral::Status::ProvedSymbolic;
                    return out;
                }
            }
        }
    }

    // 4. Dilogarithm (Spence's Li_2 / `dilog`).
    {
        Expr logArg;
        std::vector<Expr> nonLogFacs;
        for (const Expr &fac : factors) {
            if (logArg.isNull() && c.kind(fac) == NodeKind::Func &&
                c.funcName(fac) == "log") {
                logArg = c.child(fac, 0);
            } else {
                nonLogFacs.push_back(fac);
            }
        }
        if (!logArg.isNull()) {
            const Expr rest =
                nonLogFacs.empty() ? c.one() : c.mul(nonLogFacs);

            // 4a. Direct logarithmic-derivative pattern:
            //     int rest(x) * log(1 - u(x)) dx = -q * dilog(u(x))
            //     whenever q = rest(x) * u(x) / u'(x) is independent of `var`
            //     (covers int log(1 + a*exp(b*x + d)) dx, int log(1 + a*x^m)/x dx, etc.).
            const Expr uCand = c.simplify(c.add({c.one(), c.neg(logArg)}));
            if (!c.isZero(uCand)) {
                const Expr duCand = c.diff(uCand, var);
                if (!c.isZero(duCand)) {
                    const Expr q = c.simplify(c.div(c.mul({rest, uCand}), duCand));
                    if (!q.isNull() && !mentionsVar(c, q, var)) {
                        const Expr F =
                            c.simplify(c.neg(c.mul({q, c.func("dilog", uCand)})));
                        if (certifySpecialIntegral(c, F, f, var)) {
                            out.F = F;
                            out.status = RationalIntegral::Status::ProvedSymbolic;
                            return out;
                        }
                    }
                }
            }

            // 4b. Rational-logarithmic integrand: int R(x) * log(a*x + b) dx.
            std::vector<Expr> aCoeffs;
            if (extractPolyInVar(c, logArg, var, 1, aCoeffs) &&
                aCoeffs.size() == 2 && !c.isZero(aCoeffs[1])) {
                const Expr b = aCoeffs[0];
                const Expr a = aCoeffs[1];

                // Single symbolic/numeric linear pole (c1*x + c0)^(-poleK).
                std::vector<Expr> numFacs;
                Expr linBase;
                std::int64_t poleK = 0;
                for (const Expr &rf : nonLogFacs) {
                    if (poleK == 0 && c.kind(rf) == NodeKind::Pow &&
                        c.kind(c.child(rf, 1)) == NodeKind::Number) {
                        const Rational &re = c.numberValue(c.child(rf, 1));
                        std::int64_t kVal = 0;
                        std::vector<Expr> lCoeffs;
                        if (re.den() == BigInt(1) && re.num().fitsInt64(kVal) &&
                            kVal <= -1 && kVal >= -6 &&
                            extractPolyInVar(c, c.child(rf, 0), var, 1, lCoeffs) &&
                            lCoeffs.size() == 2 && !c.isZero(lCoeffs[1])) {
                            linBase = c.child(rf, 0);
                            poleK = -kVal;
                            continue;
                        }
                    }
                    numFacs.push_back(rf);
                }
                if (poleK >= 1) {
                    std::vector<Expr> lCoeffs;
                    extractPolyInVar(c, linBase, var, 1, lCoeffs);
                    const Expr numExpr =
                        numFacs.empty() ? c.one() : c.mul(numFacs);
                    Expr F;
                    if (integrateLinearLogOverLinearPole(
                            c, logArg, a, b, linBase, lCoeffs[1], lCoeffs[0],
                            poleK, numExpr, var, budget, F) &&
                        certifySpecialIntegral(c, F, f, var)) {
                        out.F = c.simplify(F);
                        out.status = RationalIntegral::Status::ProvedSymbolic;
                        return out;
                    }
                }

                // Partial-fraction decomposition when R(x) = N(x)/D(x) in Q(x)
                // and D(x) splits completely into linear factors over Q.
                UPoly N, D;
                if (toRational(c, rest, var, N, D) && !D.isZero() &&
                    D.deg() >= 1) {
                    const UPoly gnd = UPoly::gcd(N, D);
                    if (gnd.deg() >= 1) {
                        UPoly qN, rN, qD, rD;
                        UPoly::divMod(N, gnd, qN, rN);
                        UPoly::divMod(D, gnd, qD, rD);
                        N = qN;
                        D = qD;
                    }
                    const Rational dLc = D.lc();
                    UPoly dMonic = D;
                    dMonic.makeMonic();
                    N = N * UPoly({Rational(std::int64_t{1}) / dLc});
                    UPoly qPoly, rPoly;
                    UPoly::divMod(N, dMonic, qPoly, rPoly);

                    std::vector<UPoly> irreds = factorOverQ(dMonic, budget);
                    struct LinFactor
                    {
                        UPoly lin;
                        int mult = 0;
                        UPoly linPow;
                    };
                    std::vector<LinFactor> lfs;
                    bool allLinear = !(budget && !budget->ok());
                    for (const UPoly &ir : irreds) {
                        if (ir.deg() != 1) {
                            allLinear = false;
                            break;
                        }
                        bool found = false;
                        for (auto &lf : lfs) {
                            if (lf.lin == ir) {
                                lf.mult += 1;
                                lf.linPow = lf.linPow * ir;
                                found = true;
                                break;
                            }
                        }
                        if (!found)
                            lfs.push_back(LinFactor{ir, 1, ir});
                    }
                    if (allLinear && !lfs.empty()) {
                        std::vector<Expr> pfPieces;
                        bool okPF = true;
                        if (!qPoly.isZero()) {
                            const Expr elemPart = c.mul(
                                {toExpr(c, qPoly, var), c.func("log", logArg)});
                            const RationalIntegral elemInt =
                                integrate(c, elemPart, var, budget);
                            if (!elemInt.proved())
                                okPF = false;
                            else
                                pfPieces.push_back(elemInt.F);
                        }
                        for (std::size_t j = 0; j < lfs.size() && okPF; ++j) {
                            UPoly mj({Rational(std::int64_t{1})});
                            for (std::size_t i = 0; i < lfs.size(); ++i) {
                                if (i != j)
                                    mj = mj * lfs[i].linPow;
                            }
                            const UPoly invMj = UPoly::invMod(
                                mj % lfs[j].linPow, lfs[j].linPow);
                            const UPoly pj = (rPoly * invMj) % lfs[j].linPow;
                            if (pj.isZero())
                                continue;
                            const Expr c0Expr = c.number(lfs[j].lin.coeff(0));
                            const Expr c1Expr = c.number(lfs[j].lin.coeff(1));
                            const Expr linExpr =
                                c.add({c0Expr, c.mul({c1Expr, var})});
                            const Expr numPart = toExpr(c, pj, var);
                            Expr pieceF;
                            if (!integrateLinearLogOverLinearPole(
                                    c, logArg, a, b, linExpr, c1Expr, c0Expr,
                                    lfs[j].mult, numPart, var, budget,
                                    pieceF)) {
                                okPF = false;
                                break;
                            }
                            pfPieces.push_back(pieceF);
                        }
                        if (okPF) {
                            const Expr F =
                                pfPieces.empty() ? c.zero() : c.add(pfPieces);
                            if (certifySpecialIntegral(c, F, f, var)) {
                                out.F = c.simplify(F);
                                out.status =
                                    RationalIntegral::Status::ProvedSymbolic;
                                return out;
                            }
                        }
                    }
                }
            }
        }

        // 4c. Bose-Einstein / Fermi-Dirac / Debye integrand:
        //     int (p1*x + p0) / (A * exp(b*x + d) + B) dx.
        Expr expDenom;
        std::vector<Expr> numFacs;
        for (const Expr &fac : factors) {
            if (expDenom.isNull() && c.kind(fac) == NodeKind::Pow &&
                c.child(fac, 1) == c.number(std::int64_t{-1}) &&
                c.kind(c.child(fac, 0)) == NodeKind::Add &&
                c.childCount(c.child(fac, 0)) == 2) {
                expDenom = c.child(fac, 0);
            } else {
                numFacs.push_back(fac);
            }
        }
        if (!expDenom.isNull()) {
            const Expr numExpr = numFacs.empty() ? c.one() : c.mul(numFacs);
            std::vector<Expr> pCoeffs;
            if (extractPolyInVar(c, numExpr, var, 1, pCoeffs) &&
                pCoeffs.size() == 2 && !c.isZero(pCoeffs[1])) {
                Expr term0 = c.child(expDenom, 0);
                Expr term1 = c.child(expDenom, 1);
                if (mentionsVar(c, term0, var) && !mentionsVar(c, term1, var))
                    std::swap(term0, term1);
                if (!mentionsVar(c, term0, var) && mentionsVar(c, term1, var)) {
                    const Expr B = term0;
                    Expr A = c.one();
                    Expr expArg;
                    if (c.kind(term1) == NodeKind::Func &&
                        c.funcName(term1) == "exp") {
                        expArg = c.child(term1, 0);
                    } else if (c.kind(term1) == NodeKind::Mul) {
                        std::vector<Expr> aFacs;
                        for (std::size_t i = 0; i < c.childCount(term1); ++i) {
                            const Expr ch = c.child(term1, i);
                            if (expArg.isNull() && c.kind(ch) == NodeKind::Func &&
                                c.funcName(ch) == "exp") {
                                expArg = c.child(ch, 0);
                            } else {
                                aFacs.push_back(ch);
                            }
                        }
                        if (!expArg.isNull() && !aFacs.empty()) {
                            A = aFacs.size() == 1 ? aFacs[0] : c.mul(aFacs);
                        }
                    }
                    std::vector<Expr> eCoeffs;
                    if (!expArg.isNull() && !mentionsVar(c, A, var) &&
                        extractPolyInVar(c, expArg, var, 1, eCoeffs) &&
                        eCoeffs.size() == 2 && !c.isZero(eCoeffs[1])) {
                        const Expr b = eCoeffs[1];
                        const Expr p0 = pCoeffs[0];
                        const Expr p1 = pCoeffs[1];
                        const Expr expNeg = c.func("exp", c.neg(expArg));
                        const Expr u =
                            c.simplify(c.neg(c.mul({c.div(B, A), expNeg})));
                        const Expr oneMinusU =
                            c.add({c.one(), c.mul({c.div(B, A), expNeg})});
                        const Expr b2 = c.pow(b, c.number(std::int64_t{2}));
                        const Expr f1 = c.neg(c.div(
                            c.mul({p1,
                                   c.add({c.mul({b, var,
                                                 c.func("log", oneMinusU)}),
                                          c.neg(c.func("dilog", u))})}),
                            c.mul({B, b2})));
                        const Expr f0 = c.isZero(p0)
                                            ? c.zero()
                                            : c.neg(c.div(
                                                  c.mul({p0,
                                                         c.func("log", oneMinusU)}),
                                                  c.mul({B, b})));
                        const Expr F = c.add({f1, f0});
                        if (certifySpecialIntegral(c, F, f, var)) {
                            out.F = F;
                            out.status = RationalIntegral::Status::ProvedSymbolic;
                            return out;
                        }
                    }
                }
            }
        }

        // 4d. Bessel function antiderivatives:
        //     int x^(nu+1) * besselj(nu, a*x) dx = x^(nu+1)/a * besselj(nu+1, a*x)
        //     int x^(1-nu) * besselj(nu, a*x) dx = -x^(1-nu)/a * besselj(nu-1, a*x)
        //     int besselj(1, a*x) dx = -1/a * besselj(0, a*x)
        //     (and analogous formulas for bessely, besseli, besselk).
        Expr besselFac;
        std::vector<Expr> otherFacs;
        for (const Expr &fac : factors) {
            if (besselFac.isNull() && c.kind(fac) == NodeKind::Func &&
                c.childCount(fac) == 2 &&
                (c.funcName(fac) == "besselj" || c.funcName(fac) == "bessely" ||
                 c.funcName(fac) == "besseli" || c.funcName(fac) == "besselk")) {
                besselFac = fac;
            } else {
                otherFacs.push_back(fac);
            }
        }
        if (!besselFac.isNull()) {
            const std::string &bfn = c.funcName(besselFac);
            const Expr nu = c.child(besselFac, 0);
            const Expr bArg = c.child(besselFac, 1);
            std::vector<Expr> bCoeffs;
            if (!mentionsVar(c, nu, var) &&
                extractPolyInVar(c, bArg, var, 1, bCoeffs) &&
                bCoeffs.size() == 2 && c.isZero(bCoeffs[0]) &&
                !c.isZero(bCoeffs[1])) {
                const Expr aCoeff = bCoeffs[1];
                Expr xPowExp = c.zero();
                std::vector<Expr> cFacs;
                bool okOther = true;
                for (const Expr &of : otherFacs) {
                    if (!mentionsVar(c, of, var)) {
                        cFacs.push_back(of);
                    } else if (of == var) {
                        xPowExp = c.add({xPowExp, c.one()});
                    } else if (c.kind(of) == NodeKind::Pow &&
                               c.child(of, 0) == var &&
                               !mentionsVar(c, c.child(of, 1), var)) {
                        xPowExp = c.add({xPowExp, c.child(of, 1)});
                    } else {
                        okOther = false;
                        break;
                    }
                }
                if (okOther) {
                    const Expr cPart = cFacs.empty() ? c.one() : c.mul(cFacs);
                    const Expr diffUp =
                        c.simplify(c.add({xPowExp, c.neg(c.add({nu, c.one()}))}));
                    const Expr diffDown =
                        c.simplify(c.add({xPowExp, c.neg(c.add({c.one(), c.neg(nu)}))}));
                    if (c.isZero(diffUp)) {
                        const Expr nuP1 = c.simplify(c.add({nu, c.one()}));
                        Expr core = c.mul({
                            c.pow(aCoeff, c.number(-1)),
                            c.pow(var, nuP1),
                            c.func(bfn, nuP1, bArg)});
                        if (bfn == "besselk")
                            core = c.neg(core);
                        const Expr F = c.mul({cPart, core});
                        if (certifySpecialIntegral(c, F, f, var)) {
                            out.F = F;
                            out.status = RationalIntegral::Status::ProvedSymbolic;
                            return out;
                        }
                    } else if (c.isZero(diffDown)) {
                        const Expr nuM1 = c.simplify(c.add({nu, c.number(-1)}));
                        const Expr oneMinusNu =
                            c.simplify(c.add({c.one(), c.neg(nu)}));
                        Expr core = c.mul({
                            c.pow(aCoeff, c.number(-1)),
                            c.pow(var, oneMinusNu),
                            c.func(bfn, nuM1, bArg)});
                        if (bfn == "besselj" || bfn == "bessely" ||
                            bfn == "besselk")
                            core = c.neg(core);
                        const Expr F = c.mul({cPart, core});
                        if (certifySpecialIntegral(c, F, f, var)) {
                            out.F = F;
                            out.status = RationalIntegral::Status::ProvedSymbolic;
                            return out;
                        }
                    }
                }
            }
        }

        // 4e. Incomplete elliptic integrals of the 1st and 2nd kind:
        //     int (1 - m*sin(a*x + b)^2)^(-1/2) dx = 1/a * ellipticF(a*x + b, m)
        //     int (1 - m*sin(a*x + b)^2)^(1/2) dx  = 1/a * ellipticEInc(a*x + b, m)
        //     More generally: (c0 + c1*sin(u)^2 + c2*cos(u)^2)^(+/-1/2)
        //     = (A * (1 - m*sin(u)^2))^(+/-1/2) where A = c0 + c2, m = (c2 - c1)/(c0 + c2).
        Expr radFac;
        std::vector<Expr> radConstFacs;
        bool radOnly = true;
        for (const Expr &fac : factors) {
            if (!mentionsVar(c, fac, var)) {
                radConstFacs.push_back(fac);
            } else if (radFac.isNull() && c.kind(fac) == NodeKind::Pow &&
                       c.kind(c.child(fac, 1)) == NodeKind::Number) {
                const Rational &re = c.numberValue(c.child(fac, 1));
                if (re == Rational(std::int64_t{-1}, BigInt(2)) ||
                    re == Rational(std::int64_t{1}, BigInt(2))) {
                    radFac = fac;
                } else {
                    radOnly = false;
                    break;
                }
            } else {
                radOnly = false;
                break;
            }
        }
        if (radOnly && !radFac.isNull()) {
            const Rational &re = c.numberValue(c.child(radFac, 1));
            const bool isFirstKind =
                (re == Rational(std::int64_t{-1}, BigInt(2)));
            const Expr base = c.expand(c.child(radFac, 0));
            std::vector<Expr> bTerms;
            if (c.kind(base) == NodeKind::Add) {
                for (std::size_t i = 0; i < c.childCount(base); ++i)
                    bTerms.push_back(c.child(base, i));
            } else {
                bTerms.push_back(base);
            }
            Expr c0 = c.zero();
            Expr c1 = c.zero();
            Expr c2 = c.zero();
            Expr uArg;
            bool okTrigQuad = true;
            for (const Expr &bt : bTerms) {
                if (!mentionsVar(c, bt, var)) {
                    c0 = c.add({c0, bt});
                    continue;
                }
                std::vector<Expr> tFacs;
                if (c.kind(bt) == NodeKind::Mul) {
                    for (std::size_t i = 0; i < c.childCount(bt); ++i)
                        tFacs.push_back(c.child(bt, i));
                } else {
                    tFacs.push_back(bt);
                }
                std::vector<Expr> coefFacs;
                std::string trigFn;
                Expr trigU;
                bool matchedTerm = true;
                for (const Expr &tf : tFacs) {
                    if (!mentionsVar(c, tf, var)) {
                        coefFacs.push_back(tf);
                    } else if (trigFn.empty() && c.kind(tf) == NodeKind::Pow &&
                               c.child(tf, 1) == c.number(std::int64_t{2}) &&
                               c.kind(c.child(tf, 0)) == NodeKind::Func &&
                               c.childCount(c.child(tf, 0)) == 1 &&
                               (c.funcName(c.child(tf, 0)) == "sin" ||
                                c.funcName(c.child(tf, 0)) == "cos")) {
                        trigFn = c.funcName(c.child(tf, 0));
                        trigU = c.child(c.child(tf, 0), 0);
                    } else {
                        matchedTerm = false;
                        break;
                    }
                }
                if (!matchedTerm || trigFn.empty()) {
                    okTrigQuad = false;
                    break;
                }
                if (!uArg.isNull() && !(uArg == trigU)) {
                    okTrigQuad = false;
                    break;
                }
                uArg = trigU;
                const Expr termCoef =
                    coefFacs.empty() ? c.one() : c.mul(coefFacs);
                if (trigFn == "sin")
                    c1 = c.add({c1, termCoef});
                else
                    c2 = c.add({c2, termCoef});
            }
            std::vector<Expr> uCoeffs;
            if (okTrigQuad && !uArg.isNull() &&
                extractPolyInVar(c, uArg, var, 1, uCoeffs) &&
                uCoeffs.size() == 2 && !c.isZero(uCoeffs[1])) {
                const Expr aCoeff = uCoeffs[1];
                const Expr A = c.simplify(c.add({c0, c2}));
                const Expr mParam = c.simplify(
                    c.div(c.add({c2, c.neg(c1)}), A));
                if (!c.isZero(A) && !c.isZero(mParam)) {
                    Expr aScale;
                    if (A == c.one()) {
                        aScale = c.one();
                    } else if (c.kind(A) == NodeKind::Number &&
                               c.numberValue(A).signum() > 0) {
                        const Expr sqA = sqrtExpr(c, c.numberValue(A));
                        aScale = isFirstKind ? c.pow(sqA, c.number(-1)) : sqA;
                    } else if (c.isAssumedPositive(A)) {
                        aScale = c.pow(A, c.child(radFac, 1));
                    }
                    if (!aScale.isNull()) {
                        const Expr cPart = radConstFacs.empty()
                                               ? c.one()
                                               : c.mul(radConstFacs);
                        const Expr ellFn =
                            c.func(isFirstKind ? "ellipticF" : "ellipticEInc",
                                   uArg, mParam);
                        const Expr F = c.simplify(c.mul({
                            cPart, aScale, c.pow(aCoeff, c.number(-1)), ellFn}));
                        const Expr sin2U =
                            c.pow(c.func("sin", uArg), c.number(std::int64_t{2}));
                        const Expr fCanon = c.mul({
                            cPart, aScale,
                            c.pow(c.add({c.one(), c.neg(c.mul({mParam, sin2U}))}),
                                  c.child(radFac, 1))});
                        if (certifySpecialIntegral(c, F, f, var) ||
                            certifySpecialIntegral(c, F, fCanon, var)) {
                            out.F = F;
                            out.status = RationalIntegral::Status::ProvedSymbolic;
                            return out;
                        }
                    }
                }
            }
        }

        // 4f. Polylogarithm / dilogarithm antiderivatives:
        //     int rest(x) * polylog(s, u(x)) dx = q * polylog(s + 1, u(x))
        //     int rest(x) * dilog(u(x)) dx      = q * polylog(3, u(x))
        //     where q = rest(x) * u(x) / u'(x) is independent of `var`.
        Expr polylogFac;
        std::vector<Expr> polylogOtherFacs;
        for (const Expr &fac : factors) {
            if (polylogFac.isNull() && c.kind(fac) == NodeKind::Func &&
                ((c.funcName(fac) == "polylog" && c.childCount(fac) == 2 &&
                  !mentionsVar(c, c.child(fac, 0), var)) ||
                 (c.funcName(fac) == "dilog" && c.childCount(fac) == 1))) {
                polylogFac = fac;
            } else {
                polylogOtherFacs.push_back(fac);
            }
        }
        if (!polylogFac.isNull()) {
            const bool isDilog = (c.funcName(polylogFac) == "dilog");
            const Expr sOrd =
                isDilog ? c.number(std::int64_t{2}) : c.child(polylogFac, 0);
            const Expr uArg =
                isDilog ? c.child(polylogFac, 0) : c.child(polylogFac, 1);
            const Expr du = c.diff(uArg, var);
            if (!c.isZero(du)) {
                const Expr rest = polylogOtherFacs.empty()
                                      ? c.one()
                                      : c.mul(polylogOtherFacs);
                const Expr q = c.simplify(c.div(c.mul({rest, uArg}), du));
                if (!mentionsVar(c, q, var)) {
                    const Expr sNext = c.simplify(c.add({sOrd, c.one()}));
                    const Expr F =
                        c.simplify(c.mul({q, c.func("polylog", sNext, uArg)}));
                    if (certifySpecialIntegral(c, F, f, var)) {
                        out.F = F;
                        out.status = RationalIntegral::Status::ProvedSymbolic;
                        return out;
                    }
                }
            }
        }
    }

    // 5. Orthogonal / Bernoulli / Euler polynomials with concrete integer degree:
    //    expand to explicit polynomial and integrate.
    const Expr fExpanded = c.expand(f);
    if (!fExpanded.isNull() && !(fExpanded == f)) {
        return integrate(c, fExpanded, var, budget);
    }

    // 6. Symbolic-order Bernoulli and Euler polynomials:
    //    int bernoulliB(n, a*x + b) dx = bernoulliB(n + 1, a*x + b) / (a * (n + 1))
    //    int eulerE(n, a*x + b) dx     = eulerE(n + 1, a*x + b) / (a * (n + 1))
    if (c.kind(f) == NodeKind::Func && c.childCount(f) == 2 &&
        (c.funcName(f) == "bernoulliB" || c.funcName(f) == "eulerE") &&
        !mentionsVar(c, c.child(f, 0), var)) {
        const Expr nOrd = c.child(f, 0);
        const Expr uArg = c.child(f, 1);
        std::vector<Expr> uCoeffs;
        if (extractPolyInVar(c, uArg, var, 1, uCoeffs) &&
            uCoeffs.size() == 2 && !c.isZero(uCoeffs[1])) {
            const Expr nP1 = c.simplify(c.add({nOrd, c.one()}));
            if (!c.isZero(nP1)) {
                const Expr F = c.div(c.func(c.funcName(f), nP1, uArg),
                                     c.mul({uCoeffs[1], nP1}));
                if (certifySpecialIntegral(c, F, f, var)) {
                    out.F = F;
                    out.status = RationalIntegral::Status::ProvedSymbolic;
                    return out;
                }
            }
        }
    }

    // 7. Generalized hypergeometric functions:
    //    int hypergeom0F1(b, k*x + d) dx       = (b - 1)/k * hypergeom0F1(b - 1, k*x + d)
    //    int hypergeom1F1(a, b, k*x + d) dx    = (b - 1)/(k*(a - 1)) * hypergeom1F1(a - 1, b - 1, k*x + d)
    //    int hypergeom2F1(a, b, c, k*x + d) dx = (c - 1)/(k*(a - 1)*(b - 1)) * hypergeom2F1(a - 1, b - 1, c - 1, k*x + d)
    if (c.kind(f) == NodeKind::Func &&
        ((c.funcName(f) == "hypergeom0F1" && c.childCount(f) == 2) ||
         (c.funcName(f) == "hypergeom1F1" && c.childCount(f) == 3) ||
         (c.funcName(f) == "hypergeom2F1" && c.childCount(f) == 4))) {
        const std::size_t nArgs = c.childCount(f);
        bool paramsFree = true;
        for (std::size_t i = 0; i + 1 < nArgs; ++i) {
            if (mentionsVar(c, c.child(f, i), var)) {
                paramsFree = false;
                break;
            }
        }
        const Expr uArg = c.child(f, nArgs - 1);
        std::vector<Expr> uCoeffs;
        if (paramsFree && extractPolyInVar(c, uArg, var, 1, uCoeffs) &&
            uCoeffs.size() == 2 && !c.isZero(uCoeffs[1])) {
            const Expr kSlope = uCoeffs[1];
            const Expr m1 = c.number(std::int64_t{-1});
            std::vector<Expr> shiftedArgs;
            bool validShift = true;
            for (std::size_t i = 0; i + 1 < nArgs; ++i) {
                const Expr pm1 = c.simplify(c.add({c.child(f, i), m1}));
                if (c.isZero(pm1)) {
                    validShift = false;
                    break;
                }
                shiftedArgs.push_back(pm1);
            }
            if (validShift) {
                shiftedArgs.push_back(uArg);
                const Expr bM1 = shiftedArgs[nArgs - 2];
                Expr denom = kSlope;
                if (nArgs == 3)
                    denom = c.mul({kSlope, shiftedArgs[0]});
                else if (nArgs == 4)
                    denom = c.mul({kSlope, shiftedArgs[0], shiftedArgs[1]});
                const Expr F =
                    c.div(c.mul({bM1, c.func(c.funcName(f), shiftedArgs)}),
                          denom);
                if (certifySpecialIntegral(c, F, f, var)) {
                    out.F = F;
                    out.status = RationalIntegral::Status::ProvedSymbolic;
                    return out;
                }
            }
        }
    }

    return out;
}

} // namespace

RationalIntegral integrate(Ctx &c, Expr f, Expr var, Budget *budget)
{
    RationalIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;

    if (!f.isNull() && !var.isNull() && !mentionsVar(c, f, var)) {
        out.F = c.mul({f, var});
        out.status = RationalIntegral::Status::ProvedSymbolic;
        return out;
    }

    // 1. AOT Rubi rule engine fast-path (`rubiApply`).
    const Expr F_rubi =
        rubi::rubiApply(rubi::sliceTables(), c, f, var, budget);
    if (!F_rubi.isNull()) {
        out.F = F_rubi;
        out.status = RationalIntegral::Status::ProvedSymbolic;
        return out;
    }
    if (budget && !budget->ok()) {
        out.reason = budget->status() == BudgetStatus::StepExhausted
                         ? "step budget exhausted"
                         : "arena byte budget exhausted";
        return out;
    }

    // 2. Algebraic & Liouvillian kernel (`integrateRational`: Hermite +
    //    Rothstein-Trager + Rioboo + exp/log/tan/radical storeys).
    const RationalIntegral r = integrateRational(c, f, var, budget);
    if (r.proved() || (budget && !budget->ok()))
        return r;

    // 3. Constant-factor pull-out (`var`-free factors in a product whose
    //    remaining factors actually depend on `var`).
    if (c.kind(f) == NodeKind::Mul) {
        std::vector<Expr> constFactors;
        std::vector<Expr> varFactors;
        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            const Expr ch = c.child(f, i);
            if (mentionsVar(c, ch, var))
                varFactors.push_back(ch);
            else
                constFactors.push_back(ch);
        }
        if (!constFactors.empty() && !varFactors.empty()) {
            const RationalIntegral inner =
                integrate(c, c.mul(varFactors), var, budget);
            if (!inner.proved())
                return inner;
            out.F = c.mul({c.mul(constFactors), inner.F});
            out.status = RationalIntegral::Status::ProvedSymbolic;
            return out;
        }
    }

    // 4. Non-elementary Liouvillian special-function storey (`erf`, `erfi`,
    //    `Ei`, `li`, `Si`, `Ci`, `FresnelS`, `FresnelC`).
    const RationalIntegral spec = integrateSpecialFunctions(c, f, var, budget);
    if (spec.proved() || (budget && !budget->ok()))
        return spec;

    // 5. Additive linearity over `Add` (mixed sums where summands are
    //    handled by Rubi, the algebraic/Liouvillian kernel, or special functions).
    if (c.kind(f) == NodeKind::Add) {
        std::vector<Expr> pieces;
        pieces.reserve(c.childCount(f));
        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            const RationalIntegral part =
                integrate(c, c.child(f, i), var, budget);
            if (!part.proved())
                return part;
            pieces.push_back(part.F);
        }
        out.F = c.add(pieces);
        out.status = RationalIntegral::Status::ProvedSymbolic;
        return out;
    }

    return r;
}

bool factorExpr(Ctx &c, Expr e, Expr var, Expr &out)
{
    UPoly N, D;
    if (!toRational(c, e, var, N, D) || D.isZero())
        return false;

    // Monic factor powers of N and D plus the rational content:
    // e = (n_c / d_c) * prod f_i^m_i / prod g_j^e_j.
    const auto build = [&c, &var](const UPoly &p,
                                  std::vector<Expr> &factors) -> Rational {
        Rational content = p.lc();
        std::vector<UPoly> fs = factorOverQ(p);
        for (const UPoly &f : fs)
            factors.push_back(toExpr(c, f, var));
        return content;
    };
    std::vector<Expr> numFactors, denFactors;
    const Rational numContent = build(N, numFactors);
    const Rational denContent = build(D, denFactors);
    // Multiplicities: count equal factors (factorOverQ emits each
    // multiplicity copy separately).
    const auto withPowers = [&c](std::vector<Expr> &fs) {
        std::vector<Expr> out;
        std::sort(fs.begin(), fs.end(), [&c](Expr a, Expr b) {
            return c.compare(a, b) < 0;
        });
        for (std::size_t i = 0; i < fs.size();) {
            std::size_t j = i;
            while (j < fs.size() && fs[j] == fs[i])
                ++j;
            const Expr f = fs[i];
            out.push_back(j - i == 1
                              ? f
                              : c.pow(f, c.number(static_cast<std::int64_t>(j - i))));
            i = j;
        }
        return out;
    };
    std::vector<Expr> numP = withPowers(numFactors);
    std::vector<Expr> denP = withPowers(denFactors);

    // Assemble: content * prod(num) / prod(den).
    std::vector<Expr> prod{c.number(numContent)};
    for (Expr &f : numP)
        prod.push_back(f);
    if (!denP.empty()) {
        std::vector<Expr> den{c.number(denContent)};
        for (Expr &f : denP)
            den.push_back(f);
        prod.push_back(c.pow(c.mul(den), c.number(std::int64_t{-1})));
    }
    out = c.mul(prod);
    return true;
}

namespace {

bool isInfBound(const Ctx &c, Expr e, int &dirOut)
{
    if (e.isNull())
        return false;
    if (c.kind(e) == NodeKind::Symbol) {
        const std::string &nm = c.symbolName(e);
        if (nm == "inf" || nm == "oo" || nm == "infinity") {
            dirOut = +1;
            return true;
        }
    }
    if (c.kind(e) == NodeKind::Mul && c.childCount(e) == 2 &&
        c.kind(c.child(e, 0)) == NodeKind::Number &&
        c.kind(c.child(e, 1)) == NodeKind::Symbol) {
        const std::string &nm = c.symbolName(c.child(e, 1));
        if (nm == "inf" || nm == "oo" || nm == "infinity") {
            const int s = c.numberValue(c.child(e, 0)).signum();
            if (s != 0) {
                dirOut = s > 0 ? +1 : -1;
                return true;
            }
        }
    }
    return false;
}

void collectPoleDenominators(Ctx &c, Expr e, Expr var,
                             std::vector<UPoly> &polysOut)
{
    UPoly n, d;
    if (toRational(c, e, var, n, d) && !d.isZero() && d.deg() >= 1) {
        polysOut.push_back(d);
        return;
    }
    if (c.kind(e) == NodeKind::Pow &&
        c.kind(c.child(e, 1)) == NodeKind::Number &&
        c.numberValue(c.child(e, 1)) <= Rational(std::int64_t{-1})) {
        UPoly bn, bd;
        if (toRational(c, c.child(e, 0), var, bn, bd) && bd.isConst() &&
            !bd.isZero() && bn.deg() >= 1) {
            polysOut.push_back(bn);
        }
    }
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        collectPoleDenominators(c, c.child(e, i), var, polysOut);
}

// Rewrite log(u) -> log(-u) when evaluating F(var) at a finite real endpoint
// `pt` where u(pt) < 0 (realizing the log|u| antiderivative branch).
Expr realizeLogAbsAtEndpoint(Ctx &c, Expr e, Expr var, Expr pt)
{
    if (e.isNull())
        return Expr();
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Add: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            ch.push_back(realizeLogAbsAtEndpoint(c, c.child(e, i), var, pt));
        return c.add(ch);
    }
    case NodeKind::Mul: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            ch.push_back(realizeLogAbsAtEndpoint(c, c.child(e, i), var, pt));
        return c.mul(ch);
    }
    case NodeKind::Pow:
        return c.pow(realizeLogAbsAtEndpoint(c, c.child(e, 0), var, pt),
                     realizeLogAbsAtEndpoint(c, c.child(e, 1), var, pt));
    case NodeKind::Func: {
        if (c.childCount(e) != 1) {
            std::vector<Expr> args;
            args.reserve(c.childCount(e));
            for (std::size_t i = 0; i < c.childCount(e); ++i)
                args.push_back(
                    realizeLogAbsAtEndpoint(c, c.child(e, i), var, pt));
            return c.func(c.funcName(e), args);
        }
        const Expr u = realizeLogAbsAtEndpoint(c, c.child(e, 0), var, pt);
        if (c.funcName(e) == "log") {
            const Expr uAtPt = c.subs(u, var, pt);
            Rational r;
            if (c.evalExact(uAtPt, {}, r)) {
                if (r.signum() < 0)
                    return c.func("log", c.neg(u));
            } else {
                double dVal = 0.0;
                if (c.evalDouble(uAtPt, {}, dVal) && dVal < -1e-12)
                    return c.func("log", c.neg(u));
            }
        }
        return c.func(c.funcName(e), u);
    }
    }
    return e;
}

bool matchRationalMultipleOfPi(Ctx &c, Expr e, Rational &kOut)
{
    if (e.isNull())
        return false;
    if (c.isZero(e)) {
        kOut = Rational(std::int64_t{0});
        return true;
    }
    const Expr piSym = c.symbol("pi");
    if (e == piSym) {
        kOut = Rational(std::int64_t{1});
        return true;
    }
    if (c.kind(e) == NodeKind::Mul && c.childCount(e) == 2 &&
        c.kind(c.child(e, 0)) == NodeKind::Number &&
        c.child(e, 1) == piSym) {
        kOut = c.numberValue(c.child(e, 0));
        return true;
    }
    return false;
}

// Expand multiple-angle sin(n*var) and cos(n*var) (|n| <= 6) into polynomials
// in sin(var) and cos(var) so substituteTangent can rationalize them.
Expr expandMultipleAngleTrig(Ctx &c, Expr e, Expr var)
{
    if (e.isNull() || !mentionsVar(c, e, var))
        return e;
    switch (c.kind(e)) {
    case NodeKind::Number:
    case NodeKind::Symbol:
    case NodeKind::RootOf:
        return e;
    case NodeKind::Func: {
        const std::string &fn = c.funcName(e);
        if (c.childCount(e) != 1) {
            std::vector<Expr> args;
            args.reserve(c.childCount(e));
            for (std::size_t i = 0; i < c.childCount(e); ++i)
                args.push_back(expandMultipleAngleTrig(c, c.child(e, i), var));
            return c.func(fn, args);
        }
        const Expr arg = expandMultipleAngleTrig(c, c.child(e, 0), var);
        if ((fn == "sin" || fn == "cos") && c.kind(arg) == NodeKind::Mul &&
            c.childCount(arg) == 2 &&
            c.kind(c.child(arg, 0)) == NodeKind::Number &&
            c.child(arg, 1) == var) {
            const Rational &r = c.numberValue(c.child(arg, 0));
            std::int64_t n = 0;
            if (r.den() == BigInt(1) && r.num().fitsInt64(n) && n != 0 &&
                std::abs(n) <= 6) {
                const std::int64_t an = std::abs(n);
                const Expr s1 = c.func("sin", var);
                const Expr c1 = c.func("cos", var);
                Expr sn = s1, cn = c1;
                for (std::int64_t k = 2; k <= an; ++k) {
                    const Expr nextC =
                        c.add({c.mul({cn, c1}), c.neg(c.mul({sn, s1}))});
                    const Expr nextS =
                        c.add({c.mul({sn, c1}), c.mul({cn, s1})});
                    cn = nextC;
                    sn = nextS;
                }
                if (fn == "cos")
                    return cn;
                return n > 0 ? sn : c.neg(sn);
            }
        }
        return c.func(fn, arg);
    }
    case NodeKind::Pow:
        return c.pow(expandMultipleAngleTrig(c, c.child(e, 0), var),
                     expandMultipleAngleTrig(c, c.child(e, 1), var));
    case NodeKind::Add:
    case NodeKind::Mul: {
        std::vector<Expr> ch;
        ch.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            ch.push_back(expandMultipleAngleTrig(c, c.child(e, i), var));
        return c.kind(e) == NodeKind::Add ? c.add(ch) : c.mul(ch);
    }
    }
    return e;
}

bool mentionsBranchTrigOrAtan(const Ctx &c, Expr e, Expr var)
{
    if (e.isNull() || !mentionsVar(c, e, var))
        return false;
    if (c.kind(e) == NodeKind::Func) {
        const std::string &fn = c.funcName(e);
        if (fn == "atan" || fn == "acot" || fn == "tan" || fn == "cot" ||
            fn == "sec" || fn == "csc" || fn == "log") {
            return true;
        }
    }
    if (c.kind(e) == NodeKind::Pow &&
        c.kind(c.child(e, 1)) == NodeKind::Number &&
        c.numberValue(c.child(e, 1)).signum() < 0) {
        return true;
    }
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        if (mentionsBranchTrigOrAtan(c, c.child(e, i), var))
            return true;
    return false;
}

// Evaluate int_{-inf}^{+inf} ((A*x + B) / ((x - alpha)^2 + betaSq)^k) * cos(omega*x) or sin(omega*x) dx
// via upper-half-plane residue calculus at z = alpha + i*sqrt(betaSq) (Jordan's lemma).
Expr evalQuadraticFourierResidue(Ctx &c, Expr A, Expr B, Expr alpha,
                                 Expr betaSq, int k, Expr absOmega, int sgnOmega,
                                 bool isSin)
{
    Expr beta, invBeta;
    sqrtFactorPair(c, betaSq, beta, invBeta);
    const Expr piSym = c.symbol("pi");
    const Expr expDecay = c.func("exp", c.neg(c.mul({absOmega, beta})));
    std::vector<Expr> J(static_cast<std::size_t>(k + 1));
    std::vector<Expr> K(static_cast<std::size_t>(k + 1));
    J[1] = c.mul({piSym, invBeta, expDecay});
    K[1] = c.mul({piSym, expDecay});
    for (int m = 2; m <= k; ++m) {
        const Expr twoM1 = c.number(static_cast<std::int64_t>(2 * (m - 1)));
        K[static_cast<std::size_t>(m)] = c.simplify(
            c.div(c.mul({absOmega, J[static_cast<std::size_t>(m - 1)]}), twoM1));
        const Expr numJ = c.add(
            {c.mul({c.number(static_cast<std::int64_t>(2 * m - 3)),
                    J[static_cast<std::size_t>(m - 1)]}),
             c.mul({absOmega, K[static_cast<std::size_t>(m - 1)]})});
        J[static_cast<std::size_t>(m)] =
            c.simplify(c.div(numJ, c.mul({twoM1, betaSq})));
    }
    const Expr bTilde = c.simplify(c.add({B, c.mul({A, alpha})}));
    const Expr jk = J[static_cast<std::size_t>(k)];
    const Expr kk = K[static_cast<std::size_t>(k)];
    const Expr sgnExpr = c.number(static_cast<std::int64_t>(sgnOmega));
    if (c.isZero(alpha)) {
        if (!isSin)
            return c.simplify(c.mul({bTilde, jk}));
        return c.simplify(c.mul({sgnExpr, A, kk}));
    }
    const Expr wAlpha = c.mul({sgnExpr, absOmega, alpha});
    const Expr cosWA = c.simplify(c.func("cos", wAlpha));
    const Expr sinWA = c.simplify(c.func("sin", wAlpha));
    if (!isSin) {
        return c.simplify(
            c.add({c.mul({bTilde, cosWA, jk}),
                   c.neg(c.mul({sgnExpr, A, sinWA, kk}))}));
    }
    return c.simplify(
        c.add({c.mul({bTilde, sinWA, jk}), c.mul({sgnExpr, A, cosWA, kk})}));
}

bool contourFourierTerm(Ctx &c, Expr f, Expr var, Budget *budget, Expr &valOut)
{
    std::string why;
    if (!checkBudget(c, budget, why))
        return false;
    if (c.kind(f) == NodeKind::Add) {
        std::vector<Expr> parts;
        for (std::size_t i = 0; i < c.childCount(f); ++i) {
            Expr pi;
            if (!contourFourierTerm(c, c.child(f, i), var, budget, pi))
                return false;
            parts.push_back(pi);
        }
        valOut = c.simplify(c.add(parts));
        return true;
    }

    std::vector<Expr> factors;
    if (c.kind(f) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(f); ++i)
            factors.push_back(c.child(f, i));
    } else {
        factors.push_back(f);
    }

    std::string trigFn;
    Expr trigArg;
    std::vector<Expr> ratFacs;
    for (const Expr &fac : factors) {
        if (trigFn.empty() && c.kind(fac) == NodeKind::Func &&
            (c.funcName(fac) == "sin" || c.funcName(fac) == "cos") &&
            mentionsVar(c, c.child(fac, 0), var)) {
            trigFn = c.funcName(fac);
            trigArg = c.child(fac, 0);
        } else {
            ratFacs.push_back(fac);
        }
    }
    if (trigFn.empty())
        return false;

    std::vector<Expr> wCoeffs;
    if (!extractPolyInVar(c, trigArg, var, 1, wCoeffs) ||
        wCoeffs.size() != 2 || c.isZero(wCoeffs[1]))
        return false;
    const Expr phase = wCoeffs[0];
    const Expr omega = wCoeffs[1];
    const Expr ratPart = ratFacs.empty() ? c.one() : c.mul(ratFacs);
    if (!c.isZero(phase)) {
        const Expr cosP = c.simplify(c.func("cos", phase));
        const Expr sinP = c.simplify(c.func("sin", phase));
        const Expr wx = c.mul({omega, var});
        Expr vSin, vCos;
        if (!contourFourierTerm(c, c.mul({ratPart, c.func("sin", wx)}), var,
                                budget, vSin) ||
            !contourFourierTerm(c, c.mul({ratPart, c.func("cos", wx)}), var,
                                budget, vCos))
            return false;
        if (trigFn == "sin") {
            valOut = c.simplify(
                c.add({c.mul({cosP, vSin}), c.mul({sinP, vCos})}));
        } else {
            valOut = c.simplify(
                c.add({c.mul({cosP, vCos}), c.neg(c.mul({sinP, vSin}))}));
        }
        return true;
    }

    int sgnOmega = 0;
    if (isNegativeSymbolicFactor(c, omega)) {
        sgnOmega = -1;
    } else if (c.isAssumedPositive(omega)) {
        sgnOmega = +1;
    } else {
        double wVal = 0.0;
        if (c.evalDouble(omega, {}, wVal)) {
            if (wVal > 1e-12)
                sgnOmega = +1;
            else if (wVal < -1e-12)
                sgnOmega = -1;
        }
    }
    if (sgnOmega == 0)
        return false;
    const Expr absOmega = (sgnOmega < 0) ? c.neg(omega) : omega;
    const bool isSin = (trigFn == "sin");

    // Path A: Rational function R(x) = N(x) / D(x) over Q[x].
    UPoly N, D;
    if (toRational(c, ratPart, var, N, D) && !D.isZero() && D.deg() >= 1) {
        if (N.isZero()) {
            valOut = c.zero();
            return true;
        }
        const UPoly gnd = UPoly::gcd(N, D);
        if (gnd.deg() >= 1) {
            UPoly qN, rN, qD, rD;
            UPoly::divMod(N, gnd, qN, rN);
            UPoly::divMod(D, gnd, qD, rD);
            N = qN;
            D = qD;
        }
        // Jordan's lemma decay check at infinity:
        //   deg(N) <= deg(D) - 1 (and if deg(N) == deg(D) - 1 with cos, only
        //   convergent if R(x) is odd so the integral is 0).
        if (N.deg() >= D.deg())
            return false;

        std::vector<Expr> totalTerms;
        // Handle removable singularity at x = 0 for sin(omega*x) / x * ...
        if (isSin && D.coeff(0).isZero()) {
            const UPoly xPoly({Rational(std::int64_t{0}), Rational(std::int64_t{1})});
            UPoly dTilde, rX;
            UPoly::divMod(D, xPoly, dTilde, rX);
            if (dTilde.coeff(0).isZero())
                return false; // double pole at 0: sin(wx)/x^2 diverges
            const Rational c0 = N.coeff(0) / dTilde.coeff(0);
            // int_{-inf}^{inf} c0 * sin(omega*x)/x dx = c0 * sgn(omega) * pi
            totalTerms.push_back(c.mul(
                {c.number(c0 * Rational(static_cast<std::int64_t>(sgnOmega))),
                 c.symbol("pi")}));
            const UPoly remNum = N - (dTilde * UPoly({c0}));
            UPoly nNext, rNext;
            UPoly::divMod(remNum, xPoly, nNext, rNext);
            N = nNext;
            D = dTilde;
        }
        if (N.isZero()) {
            valOut = totalTerms.empty() ? c.zero() : c.simplify(c.add(totalTerms));
            return true;
        }
        if (!solveRealRoots(D).empty())
            return false; // real pole on contour
        if (!isSin && N.deg() >= D.deg() - 1) {
            // Check if N(x)/D(x) is odd (so int_{-inf}^{inf} R(x)*cos(wx) dx = 0).
            const Expr rNeg = c.subs(ratPart, var, c.neg(var));
            if (c.isZero(c.simplify(c.add({ratPart, rNeg})))) {
                valOut = totalTerms.empty() ? c.zero() : c.simplify(c.add(totalTerms));
                return true;
            }
            return false;
        }

        const Rational dLc = D.lc();
        UPoly dMonic = D;
        dMonic.makeMonic();
        N = N * UPoly({Rational(std::int64_t{1}) / dLc});

        // Factor dMonic into distinct irreducible quadratics Q_j^{m_j}.
        std::vector<UPoly> irreds = factorOverQ(dMonic, budget);
        if (budget && !budget->ok())
            return false;
        struct QuadFactor
        {
            UPoly q;
            int mult = 0;
            UPoly qPow;
        };
        std::vector<QuadFactor> qfs;
        for (const UPoly &ir : irreds) {
            if (ir.deg() != 2)
                return false;
            bool found = false;
            for (auto &qf : qfs) {
                if (qf.q == ir) {
                    qf.mult += 1;
                    qf.qPow = qf.qPow * ir;
                    found = true;
                    break;
                }
            }
            if (!found)
                qfs.push_back(QuadFactor{ir, 1, ir});
        }

        for (std::size_t j = 0; j < qfs.size(); ++j) {
            UPoly mj({Rational(std::int64_t{1})});
            for (std::size_t i = 0; i < qfs.size(); ++i) {
                if (i != j)
                    mj = mj * qfs[i].qPow;
            }
            const UPoly invMj = UPoly::invMod(mj % qfs[j].qPow, qfs[j].qPow);
            UPoly pj = (N * invMj) % qfs[j].qPow;

            const Rational bCoeff = qfs[j].q.coeff(1);
            const Rational cCoeff = qfs[j].q.coeff(0);
            const Rational alphaRat =
                -bCoeff * Rational(std::int64_t{1}, BigInt(2));
            const Rational betaSqRat = cCoeff - alphaRat * alphaRat;
            if (betaSqRat.signum() <= 0)
                return false;
            const Expr alphaExpr = c.number(alphaRat);
            const Expr betaSqExpr = c.number(betaSqRat);

            // Expand pj in powers of qfs[j].q: pj / q^m = sum_{k=1}^m (A_k x + B_k) / q^k.
            UPoly cur = pj;
            for (int k = qfs[j].mult; k >= 1 && !cur.isZero(); --k) {
                UPoly quot, rem;
                UPoly::divMod(cur, qfs[j].q, quot, rem);
                cur = quot;
                if (rem.isZero())
                    continue;
                const Expr aExpr = c.number(rem.coeff(1));
                const Expr bExpr = c.number(rem.coeff(0));
                totalTerms.push_back(evalQuadraticFourierResidue(
                    c, aExpr, bExpr, alphaExpr, betaSqExpr, k, absOmega,
                    sgnOmega, isSin));
            }
        }
        valOut = totalTerms.empty() ? c.zero() : c.simplify(c.add(totalTerms));
        return true;
    }

    // Path B: Symbolic parameter quadratic (A*x + B) / (a2*x^2 + a1*x + a0)^k.
    std::vector<Expr> numFacs;
    Expr quadBase;
    int quadK = 0;
    for (const Expr &rf : ratFacs) {
        if (quadK == 0 && c.kind(rf) == NodeKind::Pow &&
            c.kind(c.child(rf, 1)) == NodeKind::Number) {
            const Rational &re = c.numberValue(c.child(rf, 1));
            std::int64_t kVal = 0;
            std::vector<Expr> qCoeffs;
            if (re.den() == BigInt(1) && re.num().fitsInt64(kVal) &&
                kVal <= -1 && kVal >= -4 &&
                extractPolyInVar(c, c.child(rf, 0), var, 2, qCoeffs) &&
                qCoeffs.size() == 3 && !c.isZero(qCoeffs[2])) {
                quadBase = c.child(rf, 0);
                quadK = static_cast<int>(-kVal);
                continue;
            }
        }
        numFacs.push_back(rf);
    }
    if (quadK >= 1) {
        std::vector<Expr> qCoeffs, nCoeffs;
        extractPolyInVar(c, quadBase, var, 2, qCoeffs);
        const Expr numExpr = numFacs.empty() ? c.one() : c.mul(numFacs);
        if (extractPolyInVar(c, numExpr, var, 1, nCoeffs)) {
            const Expr a0 = qCoeffs[0];
            const Expr a1 = qCoeffs[1];
            const Expr a2 = qCoeffs[2];
            const Expr alpha = c.simplify(
                c.neg(c.div(a1, c.mul({c.number(std::int64_t{2}), a2}))));
            const Expr betaSq = c.simplify(
                c.add({c.div(a0, a2), c.neg(c.pow(alpha, c.number(std::int64_t{2})))}));
            if (c.isAssumedPositive(betaSq)) {
                const Expr bCoeff = nCoeffs.size() >= 1 ? nCoeffs[0] : c.zero();
                const Expr aCoeff = nCoeffs.size() >= 2 ? nCoeffs[1] : c.zero();
                if (!isSin && !c.isZero(aCoeff) && quadK == 1 &&
                    c.isZero(alpha) && c.isZero(bCoeff)) {
                    valOut = c.zero();
                    return true;
                }
                if (!isSin && quadK == 1 && !c.isZero(aCoeff))
                    return false;
                const Expr scale =
                    c.pow(a2, c.number(static_cast<std::int64_t>(-quadK)));
                const Expr res = evalQuadraticFourierResidue(
                    c, aCoeff, bCoeff, alpha, betaSq, quadK, absOmega, sgnOmega,
                    isSin);
                valOut = c.simplify(c.mul({scale, res}));
                return true;
            }
        }
    }

    return false;
}

bool matchMonomialInVar(Ctx &c, Expr e, Expr var, Expr &coefOut, Expr &expOut)
{
    if (e == var) {
        coefOut = c.one();
        expOut = c.one();
        return true;
    }
    if (c.kind(e) == NodeKind::Pow && c.child(e, 0) == var &&
        !mentionsVar(c, c.child(e, 1), var)) {
        coefOut = c.one();
        expOut = c.child(e, 1);
        return true;
    }
    if (c.kind(e) == NodeKind::Mul) {
        std::vector<Expr> cFacs;
        Expr vExp;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr ch = c.child(e, i);
            if (!mentionsVar(c, ch, var)) {
                cFacs.push_back(ch);
            } else if (vExp.isNull() && ch == var) {
                vExp = c.one();
            } else if (vExp.isNull() && c.kind(ch) == NodeKind::Pow &&
                       c.child(ch, 0) == var &&
                       !mentionsVar(c, c.child(ch, 1), var)) {
                vExp = c.child(ch, 1);
            } else {
                return false;
            }
        }
        if (!vExp.isNull()) {
            coefOut = cFacs.empty() ? c.one() : c.mul(cFacs);
            expOut = vExp;
            return true;
        }
    }
    return false;
}

bool matchBinomialInVar(Ctx &c, Expr e, Expr var, Expr &c0Out, Expr &c1Out,
                        Expr &mOut)
{
    if (c.kind(e) != NodeKind::Add || c.childCount(e) != 2)
        return false;
    Expr constPart, varPart;
    if (!mentionsVar(c, c.child(e, 0), var) &&
        mentionsVar(c, c.child(e, 1), var)) {
        constPart = c.child(e, 0);
        varPart = c.child(e, 1);
    } else if (!mentionsVar(c, c.child(e, 1), var) &&
               mentionsVar(c, c.child(e, 0), var)) {
        constPart = c.child(e, 1);
        varPart = c.child(e, 0);
    } else {
        return false;
    }
    if (!matchMonomialInVar(c, varPart, var, c1Out, mOut))
        return false;
    c0Out = constPart;
    return true;
}

// Evaluate a single multiplicative term via Euler Gamma / Beta / Wallis
// definite integral identities:
//   intervalKind == 1: [0, 1]
//   intervalKind == 2: [0, +inf)
//   intervalKind == 3: [0, pi/2]
bool tryEulerGammaBetaTerm(Ctx &c, Expr term, Expr var, int intervalKind,
                           Expr &valOut, bool &isDivergent)
{
    isDivergent = false;
    std::vector<Expr> facs;
    if (c.kind(term) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(term); ++i)
            facs.push_back(c.child(term, i));
    } else {
        facs.push_back(term);
    }

    std::vector<Expr> constFacs;
    std::vector<Expr> expArgs;
    Expr xExp = c.zero();
    std::int64_t logPow = 0;
    Expr sinExp = c.zero();
    Expr cosExp = c.zero();
    bool hasTrig = false;
    int binomCount = 0;
    Expr binC0, binC1, binM, binExp = c.zero();
    Expr bin2C0, bin2C1, bin2M, bin2Exp = c.zero();
    int expDenomCount = 0;
    Expr expDenC0, expDenC1, expDenA;

    for (const Expr &fac : facs) {
        if (!mentionsVar(c, fac, var)) {
            constFacs.push_back(fac);
            continue;
        }
        if (fac == var) {
            xExp = c.add({xExp, c.one()});
            continue;
        }
        if (c.kind(fac) == NodeKind::Pow && c.child(fac, 0) == var &&
            !mentionsVar(c, c.child(fac, 1), var)) {
            xExp = c.add({xExp, c.child(fac, 1)});
            continue;
        }
        if (c.kind(fac) == NodeKind::Func && c.funcName(fac) == "log" &&
            c.child(fac, 0) == var) {
            logPow += 1;
            continue;
        }
        if (c.kind(fac) == NodeKind::Pow &&
            c.kind(c.child(fac, 0)) == NodeKind::Func &&
            c.funcName(c.child(fac, 0)) == "log" &&
            c.child(c.child(fac, 0), 0) == var &&
            c.kind(c.child(fac, 1)) == NodeKind::Number) {
            const Rational &re = c.numberValue(c.child(fac, 1));
            std::int64_t kVal = 0;
            if (re.den() == BigInt(1) && re.num().fitsInt64(kVal) && kVal >= 1 &&
                kVal <= 20) {
                logPow += kVal;
                continue;
            }
        }
        if (c.kind(fac) == NodeKind::Func && c.funcName(fac) == "exp") {
            expArgs.push_back(c.child(fac, 0));
            continue;
        }
        if (intervalKind == 2 && expDenomCount == 0 &&
            c.kind(fac) == NodeKind::Pow &&
            c.child(fac, 1) == c.number(std::int64_t{-1}) &&
            c.kind(c.child(fac, 0)) == NodeKind::Add &&
            c.childCount(c.child(fac, 0)) == 2) {
            const Expr sumNode = c.child(fac, 0);
            Expr cPart, vPart;
            if (!mentionsVar(c, c.child(sumNode, 0), var) &&
                mentionsVar(c, c.child(sumNode, 1), var)) {
                cPart = c.child(sumNode, 0);
                vPart = c.child(sumNode, 1);
            } else if (!mentionsVar(c, c.child(sumNode, 1), var) &&
                       mentionsVar(c, c.child(sumNode, 0), var)) {
                cPart = c.child(sumNode, 1);
                vPart = c.child(sumNode, 0);
            }
            if (!cPart.isNull() && !vPart.isNull()) {
                std::vector<Expr> vFacs;
                if (c.kind(vPart) == NodeKind::Mul) {
                    for (std::size_t i = 0; i < c.childCount(vPart); ++i)
                        vFacs.push_back(c.child(vPart, i));
                } else {
                    vFacs.push_back(vPart);
                }
                std::vector<Expr> c1Facs;
                Expr eArg;
                bool okExpTerm = true;
                for (const Expr &vf : vFacs) {
                    if (!mentionsVar(c, vf, var)) {
                        c1Facs.push_back(vf);
                    } else if (eArg.isNull() && c.kind(vf) == NodeKind::Func &&
                               c.funcName(vf) == "exp" && c.childCount(vf) == 1) {
                        eArg = c.child(vf, 0);
                    } else {
                        okExpTerm = false;
                        break;
                    }
                }
                Expr aCand, oneExp;
                if (okExpTerm && !eArg.isNull() &&
                    matchMonomialInVar(c, eArg, var, aCand, oneExp) &&
                    oneExp == c.one()) {
                    expDenC0 = cPart;
                    expDenC1 = c1Facs.empty() ? c.one() : c.mul(c1Facs);
                    expDenA = aCand;
                    expDenomCount = 1;
                    continue;
                }
            }
        }
        if (intervalKind == 3) {
            std::string tFn;
            Expr tArg, tExp;
            if (c.kind(fac) == NodeKind::Func) {
                tFn = c.funcName(fac);
                tArg = c.child(fac, 0);
                tExp = c.one();
            } else if (c.kind(fac) == NodeKind::Pow &&
                       c.kind(c.child(fac, 0)) == NodeKind::Func &&
                       !mentionsVar(c, c.child(fac, 1), var)) {
                tFn = c.funcName(c.child(fac, 0));
                tArg = c.child(c.child(fac, 0), 0);
                tExp = c.child(fac, 1);
            }
            if (!tFn.empty() && tArg == var) {
                if (tFn == "sin") {
                    sinExp = c.add({sinExp, tExp});
                    hasTrig = true;
                    continue;
                }
                if (tFn == "cos") {
                    cosExp = c.add({cosExp, tExp});
                    hasTrig = true;
                    continue;
                }
                if (tFn == "tan") {
                    sinExp = c.add({sinExp, tExp});
                    cosExp = c.add({cosExp, c.neg(tExp)});
                    hasTrig = true;
                    continue;
                }
                if (tFn == "cot") {
                    cosExp = c.add({cosExp, tExp});
                    sinExp = c.add({sinExp, c.neg(tExp)});
                    hasTrig = true;
                    continue;
                }
                if (tFn == "sec") {
                    cosExp = c.add({cosExp, c.neg(tExp)});
                    hasTrig = true;
                    continue;
                }
                if (tFn == "csc") {
                    sinExp = c.add({sinExp, c.neg(tExp)});
                    hasTrig = true;
                    continue;
                }
            }
        }
        if (intervalKind == 1 || intervalKind == 2 || intervalKind == 4) {
            Expr bBase = fac;
            Expr bPow = c.one();
            if (c.kind(fac) == NodeKind::Pow &&
                !mentionsVar(c, c.child(fac, 1), var)) {
                bBase = c.child(fac, 0);
                bPow = c.child(fac, 1);
            }
            Expr c0, c1, m;
            if (matchBinomialInVar(c, bBase, var, c0, c1, m)) {
                if (binomCount == 0) {
                    binC0 = c0;
                    binC1 = c1;
                    binM = m;
                    binExp = bPow;
                    binomCount = 1;
                    continue;
                }
                if (c0 == binC0 && c1 == binC1 && m == binM) {
                    binExp = c.add({binExp, bPow});
                    continue;
                }
                if (intervalKind == 1) {
                    if (binomCount == 1) {
                        bin2C0 = c0;
                        bin2C1 = c1;
                        bin2M = m;
                        bin2Exp = bPow;
                        binomCount = 2;
                        continue;
                    }
                    if (c0 == bin2C0 && c1 == bin2C1 && m == bin2M) {
                        bin2Exp = c.add({bin2Exp, bPow});
                        continue;
                    }
                }
            }
        }
        return false;
    }

    const Expr constCoef = constFacs.empty() ? c.one() : c.mul(constFacs);

    // Interval 1: [0, 1] — Euler Beta I and log-power integrals.
    if (intervalKind == 1) {
        if (!expArgs.empty() || hasTrig)
            return false;
        if (binomCount == 0) {
            const Expr p = c.simplify(c.add({xExp, c.one()}));
            if (c.isAssumedNonNegative(c.neg(p))) {
                isDivergent = true;
                return false;
            }
            if (!c.isAssumedPositive(p) || logPow > 20)
                return false;
            BigInt fact(1);
            for (std::int64_t k = 2; k <= logPow; ++k)
                fact = fact * BigInt(k);
            if (logPow % 2 != 0)
                fact = -fact;
            valOut = c.simplify(c.mul(
                {constCoef, c.number(Rational(fact, BigInt(1))),
                 c.pow(p, c.number(-(logPow + 1)))}));
            return true;
        }
        // Polylogarithm log-power integral on [0, 1]:
        //   int_0^1 x^(k-1) * log(x)^m / (c0 + c1 * x^k) dx
        //     = (-1)^(m+1) * m! / (c1 * k^(m+1)) * polylog(m + 1, -c1 / c0)
        // for integer m >= 1, k > 0, and z = -c1/c0 <= 1.
        if (binomCount == 1 && binExp == c.number(std::int64_t{-1}) &&
            logPow >= 1 && logPow <= 20 && !c.isZero(binC0) &&
            !c.isZero(binC1) && c.isAssumedPositive(binM) &&
            c.isZero(c.simplify(c.add({xExp, c.one(), c.neg(binM)})))) {
            const Expr zArg = c.simplify(c.neg(c.div(binC1, binC0)));
            bool validZ = false;
            if (zArg == c.one()) {
                validZ = true;
            } else if (c.kind(zArg) == NodeKind::Number) {
                validZ = (c.numberValue(zArg) <= Rational(std::int64_t{1}));
            } else {
                const Expr oneMinusZ = c.simplify(c.add({c.one(), c.neg(zArg)}));
                if (c.isAssumedNonNegative(oneMinusZ)) {
                    validZ = true;
                } else {
                    double zVal = 0.0;
                    if (!c.evalDouble(zArg, {}, zVal) || zVal <= 1.0)
                        validZ = true;
                }
            }
            if (validZ) {
                BigInt fact(1);
                for (std::int64_t k = 2; k <= logPow; ++k)
                    fact = fact * BigInt(k);
                if ((logPow + 1) % 2 != 0)
                    fact = -fact;
                const Expr mPlus1 = c.number(logPow + 1);
                const Expr polyTerm = c.func("polylog", mPlus1, zArg);
                valOut = c.simplify(c.mul(
                    {constCoef, c.number(Rational(fact, BigInt(1))),
                     c.pow(binC1, c.number(std::int64_t{-1})),
                     c.pow(binM, c.number(-(logPow + 1))), polyTerm}));
                return true;
            }
        }
        if (binomCount == 1 && logPow <= 1 && binC0 == c.one() &&
            binC1 == c.number(std::int64_t{-1}) &&
            c.isAssumedPositive(binM)) {
            const Expr p = c.simplify(c.div(c.add({xExp, c.one()}), binM));
            const Expr q = c.simplify(c.add({binExp, c.one()}));
            if (c.isAssumedNonNegative(c.neg(p)) ||
                c.isAssumedNonNegative(c.neg(q))) {
                isDivergent = true;
                return false;
            }
            if (!c.isAssumedPositive(p) || !c.isAssumedPositive(q))
                return false;
            const Expr pq = c.simplify(c.add({p, q}));
            const Expr betaPart = c.div(
                c.mul({c.func("gamma", p), c.func("gamma", q)}),
                c.mul({binM, c.func("gamma", pq)}));
            if (logPow == 0) {
                valOut = c.simplify(c.mul({constCoef, betaPart}));
                return true;
            }
            const Expr psiDiff =
                c.add({c.func("digamma", p), c.neg(c.func("digamma", pq))});
            valOut =
                c.simplify(c.mul({constCoef, c.div(betaPart, binM), psiDiff}));
            return true;
        }
        // Euler's integral representation for Gauss's hypergeometric 2F1 on [0, 1]:
        //   int_0^1 x^(b-1) * (1 - x)^(c - b - 1) * (c0 + c1*x)^(-a) dx
        //     = c0^(-a) * gamma(b)*gamma(c - b)/gamma(c) * hypergeom2F1(a, b, c, -c1/c0)
        if ((binomCount == 1 || binomCount == 2) && logPow == 0 &&
            binM == c.one()) {
            Expr qMinus1 = c.zero();
            Expr zC0, zC1, negAExp;
            bool matchedEuler2F1 = false;
            if (binomCount == 1 &&
                !(binC0 == c.one() && binC1 == c.number(std::int64_t{-1}))) {
                zC0 = binC0;
                zC1 = binC1;
                negAExp = binExp;
                matchedEuler2F1 = true;
            } else if (binomCount == 2 && bin2M == c.one()) {
                if (binC0 == c.one() && binC1 == c.number(std::int64_t{-1})) {
                    qMinus1 = binExp;
                    zC0 = bin2C0;
                    zC1 = bin2C1;
                    negAExp = bin2Exp;
                    matchedEuler2F1 = true;
                } else if (bin2C0 == c.one() &&
                           bin2C1 == c.number(std::int64_t{-1})) {
                    qMinus1 = bin2Exp;
                    zC0 = binC0;
                    zC1 = binC1;
                    negAExp = binExp;
                    matchedEuler2F1 = true;
                }
            }
            if (matchedEuler2F1 && c.isAssumedPositive(zC0) &&
                !c.isZero(zC1)) {
                const Expr bParam = c.simplify(c.add({xExp, c.one()}));
                const Expr qParam = c.simplify(c.add({qMinus1, c.one()}));
                const Expr zArg = c.simplify(c.neg(c.div(zC1, zC0)));
                const Expr oneMinusZ =
                    c.simplify(c.add({c.one(), c.neg(zArg)}));
                if (c.isAssumedPositive(bParam) &&
                    c.isAssumedPositive(qParam) &&
                    c.isAssumedPositive(oneMinusZ)) {
                    const Expr aParam = c.simplify(c.neg(negAExp));
                    const Expr cParam = c.simplify(c.add({bParam, qParam}));
                    const Expr c0Scale = c.pow(zC0, negAExp);
                    const Expr betaFac = c.div(
                        c.mul({c.func("gamma", bParam),
                               c.func("gamma", qParam)}),
                        c.func("gamma", cParam));
                    const Expr hg = c.func("hypergeom2F1",
                                           {aParam, bParam, cParam, zArg});
                    valOut = c.simplify(
                        c.mul({constCoef, c0Scale, betaFac, hg}));
                    return true;
                }
            }
        }
        return false;
    }

    // Interval 2: [0, +inf) — Euler Gamma / log-Gamma, Bose-Einstein / Fermi-Dirac,
    // and Euler Beta II.
    if (intervalKind == 2) {
        if (hasTrig)
            return false;
        if (expDenomCount == 1) {
            if (!expArgs.empty() || binomCount != 0 || logPow != 0)
                return false;
            if (!c.isAssumedPositive(expDenA) || c.isZero(expDenC0) ||
                c.isZero(expDenC1))
                return false;
            const Expr s = c.simplify(c.add({xExp, c.one()}));
            const Expr zArg = c.simplify(c.neg(c.div(expDenC0, expDenC1)));
            if (zArg == c.one()) {
                // Bose-Einstein integral: int_0^inf x^(s-1) / (c1 * (exp(a*x) - 1)) dx
                //   = gamma(s) * zeta(s) / (c1 * a^s) for s > 1.
                const Expr sMinus1 = c.simplify(c.add({s, c.number(std::int64_t{-1})}));
                if (c.isAssumedNonNegative(c.neg(sMinus1))) {
                    isDivergent = true;
                    return false;
                }
                if (!c.isAssumedPositive(sMinus1))
                    return false;
                valOut = c.simplify(c.div(
                    c.mul({constCoef, c.func("gamma", s), c.func("zeta", s)}),
                    c.mul({expDenC1, c.pow(expDenA, s)})));
                return true;
            }
            if (c.isAssumedNonNegative(c.neg(s))) {
                isDivergent = true;
                return false;
            }
            if (!c.isAssumedPositive(s))
                return false;
            if (zArg == c.number(std::int64_t{-1})) {
                // Fermi-Dirac integral: int_0^inf x^(s-1) / (c1 * (exp(a*x) + 1)) dx
                //   = gamma(s) * dirichletEta(s) / (c1 * a^s) for s > 0.
                valOut = c.simplify(c.div(
                    c.mul({constCoef, c.func("gamma", s),
                           c.func("dirichletEta", s)}),
                    c.mul({expDenC1, c.pow(expDenA, s)})));
                return true;
            }
            bool validZ = false;
            if (c.kind(zArg) == NodeKind::Number) {
                validZ = (c.numberValue(zArg) < Rational(std::int64_t{1}));
            } else {
                const Expr oneMinusZ = c.simplify(c.add({c.one(), c.neg(zArg)}));
                if (c.isAssumedPositive(oneMinusZ))
                    validZ = true;
            }
            if (validZ) {
                valOut = c.simplify(c.neg(c.div(
                    c.mul({constCoef, c.func("gamma", s),
                           c.func("polylog", s, zArg)}),
                    c.mul({expDenC0, c.pow(expDenA, s)}))));
                return true;
            }
            return false;
        }
        if (!expArgs.empty() && binomCount == 0 && logPow <= 2) {
            const Expr sumExp =
                expArgs.size() == 1 ? expArgs[0] : c.simplify(c.add(expArgs));
            Expr negA, qExp;
            if (!matchMonomialInVar(c, sumExp, var, negA, qExp))
                return false;
            const Expr aCoeff = c.simplify(c.neg(negA));
            if (!c.isAssumedPositive(aCoeff) || !c.isAssumedPositive(qExp))
                return false;
            const Expr s = c.simplify(c.div(c.add({xExp, c.one()}), qExp));
            if (c.isAssumedNonNegative(c.neg(s))) {
                isDivergent = true;
                return false;
            }
            if (!c.isAssumedPositive(s))
                return false;
            const Expr baseG = c.div(
                c.func("gamma", s),
                c.mul({qExp, c.pow(aCoeff, s)}));
            if (logPow == 0) {
                valOut = c.simplify(c.mul({constCoef, baseG}));
                return true;
            }
            const Expr shiftedPsi =
                c.add({c.func("digamma", s), c.neg(c.func("log", aCoeff))});
            if (logPow == 1) {
                valOut = c.simplify(
                    c.mul({constCoef, c.div(baseG, qExp), shiftedPsi}));
                return true;
            }
            const Expr secondFactor = c.add(
                {c.pow(shiftedPsi, c.number(std::int64_t{2})),
                 c.func("trigamma", s)});
            valOut = c.simplify(c.mul(
                {constCoef,
                 c.div(baseG, c.pow(qExp, c.number(std::int64_t{2}))),
                 secondFactor}));
            return true;
        }
        if (expArgs.empty() && binomCount == 1 && logPow == 0) {
            if (!c.isAssumedPositive(binC0) || !c.isAssumedPositive(binC1) ||
                !c.isAssumedPositive(binM))
                return false;
            const Expr gammaExp = c.simplify(c.neg(binExp));
            const Expr p = c.simplify(c.div(c.add({xExp, c.one()}), binM));
            const Expr q = c.simplify(c.add({gammaExp, c.neg(p)}));
            if (c.isAssumedNonNegative(c.neg(p)) ||
                c.isAssumedNonNegative(c.neg(q))) {
                isDivergent = true;
                return false;
            }
            if (!c.isAssumedPositive(p) || !c.isAssumedPositive(q))
                return false;
            const Expr c0Pow =
                c.pow(binC0, c.simplify(c.add({p, c.neg(gammaExp)})));
            const Expr c1Pow = c.pow(binC1, c.neg(p));
            const Expr beta2 = c.div(
                c.mul({c0Pow, c1Pow, c.func("gamma", p), c.func("gamma", q)}),
                c.mul({binM, c.func("gamma", gammaExp)}));
            valOut = c.simplify(c.mul({constCoef, beta2}));
            return true;
        }
        return false;
    }

    // Interval 3: [0, pi/2] — Wallis / Trigonometric Beta integral.
    if (intervalKind == 3) {
        if (!expArgs.empty() || binomCount != 0 || logPow != 0 ||
            !c.isZero(c.simplify(xExp)) || !hasTrig)
            return false;
        const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
        const Expr p = c.simplify(c.mul({half, c.add({sinExp, c.one()})}));
        const Expr q = c.simplify(c.mul({half, c.add({cosExp, c.one()})}));
        if (c.isAssumedNonNegative(c.neg(p)) ||
            c.isAssumedNonNegative(c.neg(q))) {
            isDivergent = true;
            return false;
        }
        if (!c.isAssumedPositive(p) || !c.isAssumedPositive(q))
            return false;
        const Expr pq = c.simplify(c.add({p, q}));
        const Expr wallis = c.mul(
            {half,
             c.div(c.mul({c.func("gamma", p), c.func("gamma", q)}),
                   c.func("gamma", pq))});
        valOut = c.simplify(c.mul({constCoef, wallis}));
        return true;
    }

    // Interval 4: [-1, 1] — symmetric Jacobi / Chebyshev / Gegenbauer integral
    // int_{-1}^{1} x^k * (1 - x^2)^beta dx.
    if (intervalKind == 4) {
        if (!expArgs.empty() || hasTrig || logPow != 0)
            return false;
        const Expr kExpr = c.simplify(xExp);
        std::int64_t kInt = 0;
        if (c.kind(kExpr) != NodeKind::Number ||
            c.numberValue(kExpr).den() != BigInt(1) ||
            !c.numberValue(kExpr).num().fitsInt64(kInt) || kInt < 0)
            return false;
        Expr beta = c.zero();
        if (binomCount == 1) {
            if (binC0 != c.one() || binC1 != c.number(std::int64_t{-1}) ||
                binM != c.number(std::int64_t{2}))
                return false;
            beta = c.simplify(binExp);
        }
        const Expr q = c.simplify(c.add({beta, c.one()}));
        if (c.isAssumedNonNegative(c.neg(q))) {
            isDivergent = true;
            return false;
        }
        if (!c.isAssumedPositive(q))
            return false;
        if (kInt % 2 != 0) {
            valOut = c.zero();
            return true;
        }
        const Expr p =
            c.number(Rational(kInt + 1, BigInt(2)));
        const Expr pq = c.simplify(c.add({p, q}));
        const Expr betaVal = c.div(
            c.mul({c.func("gamma", p), c.func("gamma", q)}),
            c.func("gamma", pq));
        valOut = c.simplify(c.mul({constCoef, betaVal}));
        return true;
    }

    // Interval 5: (-inf, +inf) — bilateral Gaussian moment / Hermite integral
    // int_{-inf}^{+inf} x^k * exp(-a * x^2) dx.
    if (intervalKind == 5) {
        if (expArgs.empty() || binomCount != 0 || hasTrig || logPow != 0)
            return false;
        const Expr kExpr = c.simplify(xExp);
        std::int64_t kInt = 0;
        if (c.kind(kExpr) != NodeKind::Number ||
            c.numberValue(kExpr).den() != BigInt(1) ||
            !c.numberValue(kExpr).num().fitsInt64(kInt) || kInt < 0)
            return false;
        const Expr sumExp =
            expArgs.size() == 1 ? expArgs[0] : c.simplify(c.add(expArgs));
        Expr negA, qExp;
        if (!matchMonomialInVar(c, sumExp, var, negA, qExp) ||
            qExp != c.number(std::int64_t{2}))
            return false;
        const Expr aCoeff = c.simplify(c.neg(negA));
        if (!c.isAssumedPositive(aCoeff))
            return false;
        if (kInt % 2 != 0) {
            valOut = c.zero();
            return true;
        }
        const Expr s = c.number(Rational(kInt + 1, BigInt(2)));
        const Expr gaussVal =
            c.div(c.func("gamma", s), c.pow(aCoeff, s));
        valOut = c.simplify(c.mul({constCoef, gaussVal}));
        return true;
    }

    return false;
}

bool tryEllipticDefiniteTerm(Ctx &c, Expr term, Expr var, int intervalKind,
                             Expr &valOut)
{
    if (intervalKind != 1 && intervalKind != 3)
        return false;

    std::vector<Expr> rawFacs;
    if (c.kind(term) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(term); ++i)
            rawFacs.push_back(c.child(term, i));
    } else {
        rawFacs.push_back(term);
    }

    std::vector<Expr> facs;
    for (const Expr &rf : rawFacs) {
        if (c.kind(rf) == NodeKind::Pow &&
            c.kind(c.child(rf, 0)) == NodeKind::Mul &&
            !mentionsVar(c, c.child(rf, 1), var)) {
            const Expr baseMul = c.child(rf, 0);
            const Expr expExpr = c.child(rf, 1);
            for (std::size_t i = 0; i < c.childCount(baseMul); ++i)
                facs.push_back(c.pow(c.child(baseMul, i), expExpr));
            continue;
        }
        if (intervalKind == 1 && c.kind(rf) == NodeKind::Pow &&
            !mentionsVar(c, c.child(rf, 1), var)) {
            std::vector<Expr> qCoeffs;
            if (extractPolyInVar(c, c.child(rf, 0), var, 4, qCoeffs) &&
                qCoeffs.size() == 5 && qCoeffs[0] == c.one() &&
                c.isZero(qCoeffs[1]) && c.isZero(qCoeffs[3])) {
                const Expr mCand = qCoeffs[4];
                const Expr sumCheck = c.simplify(
                    c.add({qCoeffs[2], c.one(), mCand}));
                if (c.isZero(sumCheck)) {
                    const Expr x2 = c.pow(var, c.number(std::int64_t{2}));
                    const Expr expExpr = c.child(rf, 1);
                    facs.push_back(
                        c.pow(c.add({c.one(), c.neg(x2)}), expExpr));
                    facs.push_back(c.pow(
                        c.add({c.one(), c.neg(c.mul({mCand, x2}))}), expExpr));
                    continue;
                }
            }
        }
        facs.push_back(rf);
    }

    struct QuadBinom {
        Expr param;
        Rational exp;
    };
    std::vector<Expr> constFacs;
    std::vector<QuadBinom> bins;

    auto addBin = [&](Expr param, const Rational &re) {
        const Expr sp = c.simplify(param);
        for (QuadBinom &qb : bins) {
            if (qb.param == sp) {
                qb.exp = qb.exp + re;
                return;
            }
        }
        bins.push_back({sp, re});
    };

    for (const Expr &fac : facs) {
        if (!mentionsVar(c, fac, var)) {
            constFacs.push_back(fac);
            continue;
        }
        Expr bBase = fac;
        Rational bExp(1);
        if (c.kind(fac) == NodeKind::Pow) {
            if (c.kind(c.child(fac, 1)) != NodeKind::Number)
                return false;
            bBase = c.child(fac, 0);
            bExp = c.numberValue(c.child(fac, 1));
        }
        if (intervalKind == 1) {
            std::vector<Expr> pCoeffs;
            if (!extractPolyInVar(c, bBase, var, 2, pCoeffs) ||
                pCoeffs.size() != 3 || !(pCoeffs[0] == c.one()) ||
                !c.isZero(pCoeffs[1]) || c.isZero(pCoeffs[2])) {
                return false;
            }
            addBin(c.neg(pCoeffs[2]), bExp);
        } else {
            // intervalKind == 3: match 1 - param * sin(var)^2
            const Expr expBase = c.expand(bBase);
            if (c.kind(expBase) != NodeKind::Add || c.childCount(expBase) != 2)
                return false;
            Expr cTerm, sTerm;
            for (std::size_t i = 0; i < 2; ++i) {
                const Expr ch = c.child(expBase, i);
                if (!mentionsVar(c, ch, var))
                    cTerm = ch;
                else
                    sTerm = ch;
            }
            if (!(cTerm == c.one()) || sTerm.isNull())
                return false;
            std::vector<Expr> sFacs;
            if (c.kind(sTerm) == NodeKind::Mul) {
                for (std::size_t i = 0; i < c.childCount(sTerm); ++i)
                    sFacs.push_back(c.child(sTerm, i));
            } else {
                sFacs.push_back(sTerm);
            }
            std::vector<Expr> pFacs;
            bool hasSin2 = false;
            for (const Expr &sf : sFacs) {
                if (!mentionsVar(c, sf, var)) {
                    pFacs.push_back(sf);
                } else if (!hasSin2 && c.kind(sf) == NodeKind::Pow &&
                           c.child(sf, 1) == c.number(std::int64_t{2}) &&
                           c.kind(c.child(sf, 0)) == NodeKind::Func &&
                           c.funcName(c.child(sf, 0)) == "sin" &&
                           c.childCount(c.child(sf, 0)) == 1 &&
                           c.child(c.child(sf, 0), 0) == var) {
                    hasSin2 = true;
                } else {
                    return false;
                }
            }
            if (!hasSin2)
                return false;
            const Expr coef = pFacs.empty() ? c.one() : c.mul(pFacs);
            addBin(c.neg(coef), bExp);
        }
    }

    auto validParamBelowOne = [&](Expr p, bool allowOne) -> bool {
        double dVal = 0.0;
        if (c.evalDouble(p, {}, dVal)) {
            if (allowOne ? (dVal > 1.0 + 1e-12) : (dVal >= 1.0 - 1e-12))
                return false;
        }
        return true;
    };

    const Expr constCoef = constFacs.empty() ? c.one() : c.mul(constFacs);
    const Rational negHalf(std::int64_t{-1}, BigInt(2));
    const Rational posHalf(std::int64_t{1}, BigInt(2));
    const Rational negOne(std::int64_t{-1}, BigInt(1));

    if (intervalKind == 1) {
        int unitIdx = -1;
        for (std::size_t i = 0; i < bins.size(); ++i) {
            if (bins[i].param == c.one() && bins[i].exp == negHalf) {
                unitIdx = static_cast<int>(i);
                break;
            }
        }
        if (unitIdx < 0)
            return false;
        std::vector<QuadBinom> rem;
        for (std::size_t i = 0; i < bins.size(); ++i) {
            if (static_cast<int>(i) != unitIdx && !bins[i].exp.isZero())
                rem.push_back(bins[i]);
        }
        if (rem.size() == 1) {
            const Expr m = rem[0].param;
            if (rem[0].exp == negHalf && validParamBelowOne(m, false)) {
                valOut = c.simplify(c.mul({constCoef, c.func("ellipticK", m)}));
                return true;
            }
            if (rem[0].exp == posHalf && validParamBelowOne(m, true)) {
                valOut = c.simplify(c.mul({constCoef, c.func("ellipticE", m)}));
                return true;
            }
        } else if (rem.size() == 2) {
            int nIdx = -1, mIdx = -1;
            for (int i = 0; i < 2; ++i) {
                if (rem[static_cast<std::size_t>(i)].exp == negOne)
                    nIdx = i;
                else if (rem[static_cast<std::size_t>(i)].exp == negHalf)
                    mIdx = i;
            }
            if (nIdx >= 0 && mIdx >= 0) {
                const Expr n = rem[static_cast<std::size_t>(nIdx)].param;
                const Expr m = rem[static_cast<std::size_t>(mIdx)].param;
                if (validParamBelowOne(n, false) && validParamBelowOne(m, false)) {
                    valOut = c.simplify(
                        c.mul({constCoef, c.func("ellipticPi", n, m)}));
                    return true;
                }
            }
        }
        return false;
    }

    // intervalKind == 3 ([0, pi/2]):
    std::vector<QuadBinom> nz;
    for (const QuadBinom &qb : bins) {
        if (!qb.exp.isZero())
            nz.push_back(qb);
    }
    if (nz.size() == 1) {
        const Expr m = nz[0].param;
        if (nz[0].exp == negHalf && validParamBelowOne(m, false)) {
            valOut = c.simplify(c.mul({constCoef, c.func("ellipticK", m)}));
            return true;
        }
        if (nz[0].exp == posHalf && validParamBelowOne(m, true)) {
            valOut = c.simplify(c.mul({constCoef, c.func("ellipticE", m)}));
            return true;
        }
        if (nz[0].exp == negOne && validParamBelowOne(m, false)) {
            valOut = c.simplify(
                c.mul({constCoef, c.func("ellipticPi", m, c.zero())}));
            return true;
        }
    } else if (nz.size() == 2) {
        int nIdx = -1, mIdx = -1;
        for (int i = 0; i < 2; ++i) {
            if (nz[static_cast<std::size_t>(i)].exp == negOne)
                nIdx = i;
            else if (nz[static_cast<std::size_t>(i)].exp == negHalf)
                mIdx = i;
        }
        if (nIdx >= 0 && mIdx >= 0) {
            const Expr n = nz[static_cast<std::size_t>(nIdx)].param;
            const Expr m = nz[static_cast<std::size_t>(mIdx)].param;
            if (validParamBelowOne(n, false) && validParamBelowOne(m, false)) {
                valOut = c.simplify(
                    c.mul({constCoef, c.func("ellipticPi", n, m)}));
                return true;
            }
        }
    }
    return false;
}

bool tryEulerGammaBetaDefiniteIntegral(Ctx &c, Expr f, Expr var, Expr a, Expr b,
                                       bool aIsInf, int aInfDir, bool bIsInf,
                                       int bInfDir, DefiniteIntegral &out)
{
    int intervalKind = 0;
    int orientSign = 1;
    if (!aIsInf && !bIsInf) {
        if (c.isZero(a) && b == c.one()) {
            intervalKind = 1;
            orientSign = +1;
        } else if (a == c.one() && c.isZero(b)) {
            intervalKind = 1;
            orientSign = -1;
        } else if (a == c.number(std::int64_t{-1}) && b == c.one()) {
            intervalKind = 4;
            orientSign = +1;
        } else if (a == c.one() && b == c.number(std::int64_t{-1})) {
            intervalKind = 4;
            orientSign = -1;
        } else {
            Rational aPi, bPi;
            if (matchRationalMultipleOfPi(c, a, aPi) &&
                matchRationalMultipleOfPi(c, b, bPi)) {
                const Rational half(std::int64_t{1}, BigInt(2));
                if (aPi.isZero() && bPi == half) {
                    intervalKind = 3;
                    orientSign = +1;
                } else if (aPi == half && bPi.isZero()) {
                    intervalKind = 3;
                    orientSign = -1;
                }
            }
        }
    } else if (c.isZero(a) && bIsInf && bInfDir > 0) {
        intervalKind = 2;
        orientSign = +1;
    } else if (aIsInf && aInfDir > 0 && c.isZero(b)) {
        intervalKind = 2;
        orientSign = -1;
    } else if (aIsInf && aInfDir < 0 && bIsInf && bInfDir > 0) {
        intervalKind = 5;
        orientSign = +1;
    } else if (aIsInf && aInfDir > 0 && bIsInf && bInfDir < 0) {
        intervalKind = 5;
        orientSign = -1;
    }
    if (intervalKind == 0)
        return false;

    Expr ellDirect;
    if (tryEllipticDefiniteTerm(c, f, var, intervalKind, ellDirect)) {
        out.value = c.simplify(
            orientSign > 0 ? ellDirect : c.neg(ellDirect));
        out.status = DefiniteIntegral::Status::ProvedSymbolic;
        return true;
    }

    const Expr fWork = c.expand(f);
    const Expr fUse = fWork.isNull() ? f : fWork;
    std::vector<Expr> terms;
    if (c.kind(fUse) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(fUse); ++i)
            terms.push_back(c.child(fUse, i));
    } else {
        terms.push_back(fUse);
    }

    std::vector<Expr> pieceVals;
    pieceVals.reserve(terms.size());
    for (const Expr &t : terms) {
        Expr val;
        bool isDiv = false;
        if (!tryEulerGammaBetaTerm(c, t, var, intervalKind, val, isDiv) &&
            !tryEllipticDefiniteTerm(c, t, var, intervalKind, val)) {
            if (isDiv && terms.size() == 1) {
                out.status = DefiniteIntegral::Status::Divergent;
                out.reason = "divergent Euler Gamma/Beta integral";
                return true;
            }
            return false;
        }
        pieceVals.push_back(val);
    }
    const Expr total =
        pieceVals.size() == 1 ? pieceVals[0] : c.add(pieceVals);
    out.value = c.simplify(
        orientSign > 0 ? total : c.neg(total));
    out.status = DefiniteIntegral::Status::ProvedSymbolic;
    return true;
}

} // namespace

DefiniteIntegral definiteIntegrate(Ctx &c, Expr f, Expr var, Expr a, Expr b,
                                   Budget *budget)
{
    DefiniteIntegral out;
    if (f.isNull() || var.isNull() || a.isNull() || b.isNull()) {
        out.reason = "null input expression";
        return out;
    }
    if (!checkBudget(c, budget, out.reason))
        return out;

    int aInfDir = 0, bInfDir = 0;
    const bool aIsInf = isInfBound(c, a, aInfDir);
    const bool bIsInf = isInfBound(c, b, bInfDir);
    if (!aIsInf && !bIsInf && a == b) {
        out.status = DefiniteIntegral::Status::ProvedSymbolic;
        out.value = c.zero();
        return out;
    }

    double aVal = 0.0, bVal = 0.0;
    bool hasNumA = false, hasNumB = false;
    if (aIsInf) {
        aVal = aInfDir > 0 ? HUGE_VAL : -HUGE_VAL;
        hasNumA = true;
    } else {
        hasNumA = c.evalDouble(a, {}, aVal);
    }
    if (bIsInf) {
        bVal = bInfDir > 0 ? HUGE_VAL : -HUGE_VAL;
        hasNumB = true;
    } else {
        hasNumB = c.evalDouble(b, {}, bVal);
    }

    // 1. Interior pole guard on (min(a,b), max(a,b)).
    if (hasNumA && hasNumB) {
        const double xMin = std::min(aVal, bVal);
        const double xMax = std::max(aVal, bVal);
        std::vector<UPoly> denPolys;
        collectPoleDenominators(c, f, var, denPolys);
        for (const UPoly &D : denPolys) {
            const std::vector<RealRootSolution> roots = solveRealRoots(D);
            for (const RealRootSolution &rt : roots) {
                double rLo = 0.0, rHi = 0.0;
                if (rt.isRational) {
                    rLo = rHi = rt.value.toDouble();
                } else {
                    const RootInterval iv = refineRoot(
                        rt.carrier, rt.interval,
                        Rational(std::int64_t{1}, BigInt(1000000)));
                    rLo = iv.lo.toDouble();
                    rHi = iv.hi.toDouble();
                }
                if (rLo > xMin + 1e-11 && rHi < xMax - 1e-11) {
                    if (rt.isRational) {
                        const LimitResult limPole =
                            limit(c, f, var, c.number(rt.value), budget);
                        if (limPole.proved())
                            continue; // removable singularity
                    }
                    out.status = DefiniteIntegral::Status::Divergent;
                    out.reason = "divergent interior pole on integration interval";
                    return out;
                }
            }
        }
    }

    // 2. Compute certified indefinite antiderivative F(var).
    const RationalIntegral indef = integrate(c, f, var, budget);

    // 2a. Unit-circle / Cayley contour transformation for periodic rational
    //     trigonometric integrals R(cos(var), sin(var)) over [a, a + 2*k*pi]
    //     or [0, pi] when the indefinite antiderivative crosses the Weierstrass
    //     branch cut t = tan(var/2) at var = pi (or when indef was not found).
    if (!aIsInf && !bIsInf) {
        Rational diffPi;
        if (matchRationalMultipleOfPi(
                c, c.simplify(c.add({b, c.neg(a)})), diffPi)) {
            std::int64_t mPi = 0;
            const bool isFullPeriods =
                diffPi.den() == BigInt(1) && diffPi.num().fitsInt64(mPi) &&
                mPi != 0 && (mPi % 2 == 0);
            Rational aPi, bPi;
            const bool isHalfPeriod0Pi =
                matchRationalMultipleOfPi(c, a, aPi) &&
                matchRationalMultipleOfPi(c, b, bPi) &&
                ((aPi.isZero() && bPi == Rational(std::int64_t{1})) ||
                 (aPi == Rational(std::int64_t{1}) && bPi.isZero()));
            if ((isFullPeriods || isHalfPeriod0Pi) &&
                (!indef.proved() || mentionsBranchTrigOrAtan(c, indef.F, var))) {
                const Expr tSym = c.symbol("_t_uc");
                bool okTan = true;
                const Expr fTrig = expandMultipleAngleTrig(c, f, var);
                const Expr g = substituteTangent(c, fTrig, var, tSym, okTan);
                if (okTan) {
                    const LimitResult limPi =
                        limitOneSided(c, f, var, c.symbol("pi"), -1, budget);
                    if (limPi.status == LimitResult::Status::Divergent) {
                        out.status = DefiniteIntegral::Status::Divergent;
                        out.reason = "divergent trigonometric pole at pi";
                        return out;
                    }
                    const Expr t2p1 =
                        c.add({c.one(), c.pow(tSym, c.number(std::int64_t{2}))});
                    const Expr gJac =
                        c.div(c.mul({c.number(std::int64_t{2}), g}), t2p1);
                    const Expr infSym = c.symbol("inf");
                    const Expr loT = isFullPeriods ? c.neg(infSym) : c.zero();
                    const DefiniteIntegral sub =
                        definiteIntegrate(c, gJac, tSym, loT, infSym, budget);
                    if (sub.status == DefiniteIntegral::Status::Divergent)
                        return sub;
                    if (sub.proved()) {
                        const std::int64_t factor =
                            isFullPeriods ? (mPi / 2)
                                          : (aPi.isZero() ? std::int64_t{1}
                                                          : std::int64_t{-1});
                        out.F = indef.F;
                        out.value = c.simplify(
                            c.mul({c.number(factor), sub.value}));
                        out.status = DefiniteIntegral::Status::ProvedSymbolic;
                        return out;
                    }
                }
            }
        }
    }

    // 2b. Upper-half-plane Jordan's lemma contour integration for Fourier
    //     integrals int_{-inf}^{+inf} R(x)*cos(w*x)/sin(w*x) dx and even
    //     half-line integrals int_0^{+inf} R(x)*cos(w*x)/sin(w*x) dx.
    if (!indef.proved()) {
        const bool fullLine =
            aIsInf && bIsInf && aInfDir != bInfDir;
        const bool halfLineZeroInf =
            (c.isZero(a) && bIsInf) || (aIsInf && c.isZero(b));
        if (fullLine || halfLineZeroInf) {
            bool canContour = fullLine;
            int orientSign = 1;
            if (fullLine) {
                orientSign = (aInfDir < 0 && bInfDir > 0) ? +1 : -1;
            } else {
                // On [0, +inf) or (-inf, 0], require f(-x) == f(x) (even integrand).
                const Expr fNeg = c.subs(f, var, c.neg(var));
                if (c.isZero(c.simplify(c.add({f, c.neg(fNeg)})))) {
                    canContour = true;
                    orientSign = (c.isZero(a) && bInfDir > 0) ||
                                         (aInfDir < 0 && c.isZero(b))
                                     ? +1
                                     : -1;
                }
            }
            if (canContour) {
                Expr val;
                if (contourFourierTerm(c, c.expand(f), var, budget, val)) {
                    const Rational scale =
                        fullLine
                            ? Rational(static_cast<std::int64_t>(orientSign))
                            : Rational(static_cast<std::int64_t>(orientSign),
                                       BigInt(2));
                    out.value = c.simplify(c.mul({c.number(scale), val}));
                    out.status = DefiniteIntegral::Status::ProvedSymbolic;
                    return out;
                }
            }
        }
        if (tryEulerGammaBetaDefiniteIntegral(c, f, var, a, b, aIsInf, aInfDir,
                                              bIsInf, bInfDir, out)) {
            return out;
        }
        out.reason = indef.reason;
        return out;
    }
    out.F = indef.F;

    // 3. Evaluate endpoint limits lim_{x -> b^-} F(x) - lim_{x -> a^+} F(x).
    const int dirA = (hasNumA && hasNumB && bVal < aVal) ? -1 : +1;
    const int dirB = -dirA;

    auto evalEndpoint = [&](Expr bound, bool isInf, int infDir,
                            int approachDir) -> LimitResult {
        if (isInf)
            return limitAtInfinity(c, indef.F, var, infDir, budget);
        const Expr fReal = realizeLogAbsAtEndpoint(c, indef.F, var, bound);
        LimitResult lim1 = limitOneSided(c, fReal, var, bound, approachDir, budget);
        if (lim1.status != LimitResult::Status::Unevaluated)
            return lim1;
        return limit(c, fReal, var, bound, budget);
    };

    const LimitResult limB = evalEndpoint(b, bIsInf, bInfDir, dirB);
    if (limB.status == LimitResult::Status::Divergent) {
        out.status = DefiniteIntegral::Status::Divergent;
        out.reason = "divergent at upper integration bound";
        return out;
    }
    if (!limB.proved()) {
        if (tryEulerGammaBetaDefiniteIntegral(c, f, var, a, b, aIsInf, aInfDir,
                                              bIsInf, bInfDir, out)) {
            return out;
        }
        out.reason = limB.reason.empty()
                         ? "unable to evaluate antiderivative at upper bound"
                         : limB.reason;
        return out;
    }

    const LimitResult limA = evalEndpoint(a, aIsInf, aInfDir, dirA);
    if (limA.status == LimitResult::Status::Divergent) {
        out.status = DefiniteIntegral::Status::Divergent;
        out.reason = "divergent at lower integration bound";
        return out;
    }
    if (!limA.proved()) {
        if (tryEulerGammaBetaDefiniteIntegral(c, f, var, a, b, aIsInf, aInfDir,
                                              bIsInf, bInfDir, out)) {
            return out;
        }
        out.reason = limA.reason.empty()
                         ? "unable to evaluate antiderivative at lower bound"
                         : limA.reason;
        return out;
    }

    std::vector<Expr> jumpTerms{limB.value, c.neg(limA.value)};
    if (hasNumA && hasNumB) {
        const double xMin = std::min(aVal, bVal);
        const double xMax = std::max(aVal, bVal);
        std::vector<UPoly> fDenPolys;
        collectPoleDenominators(c, indef.F, var, fDenPolys);
        std::vector<Rational> jumpPts;
        for (const UPoly &D : fDenPolys) {
            const std::vector<RealRootSolution> roots = solveRealRoots(D);
            for (const RealRootSolution &rt : roots) {
                if (!rt.isRational)
                    continue;
                const double rVal = rt.value.toDouble();
                if (rVal > xMin + 1e-11 && rVal < xMax - 1e-11) {
                    bool seen = false;
                    for (const Rational &prev : jumpPts) {
                        if (prev == rt.value) {
                            seen = true;
                            break;
                        }
                    }
                    if (!seen)
                        jumpPts.push_back(rt.value);
                }
            }
        }
        for (const Rational &ptRat : jumpPts) {
            const Expr ptExpr = c.number(ptRat);
            const LimitResult limLeft = evalEndpoint(ptExpr, false, 0, dirB);
            const LimitResult limRight = evalEndpoint(ptExpr, false, 0, dirA);
            if (limLeft.proved() && limRight.proved()) {
                jumpTerms.push_back(limLeft.value);
                jumpTerms.push_back(c.neg(limRight.value));
            }
        }
    }

    out.value = c.simplify(c.add(jumpTerms));
    out.status = DefiniteIntegral::Status::ProvedSymbolic;
    return out;
}

RationalIntegral integrateMulti(Ctx &c, Expr f, const std::vector<Expr> &vars,
                                Budget *budget)
{
    RationalIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (f.isNull()) {
        out.reason = "null integrand";
        return out;
    }
    if (vars.empty()) {
        out.reason = "empty variable list";
        return out;
    }
    for (Expr v : vars) {
        if (v.isNull() || c.kind(v) != NodeKind::Symbol) {
            out.reason = "integration variable must be a symbol";
            return out;
        }
    }

    Expr cur = f;
    for (Expr v : vars) {
        const RationalIntegral step = integrate(c, cur, v, budget);
        if (!step.proved()) {
            out.reason = step.reason;
            return out;
        }
        cur = c.simplify(step.F);
    }

    // Certify mixed partial derivative d^k F / (d(vars[k-1]) ... d(vars[0])) == f.
    Expr dF = cur;
    for (std::size_t idx = vars.size(); idx > 0; --idx) {
        dF = c.diff(dF, vars[idx - 1]);
        if (dF.isNull()) {
            out.reason = "mixed derivative certification failed";
            return out;
        }
    }
    const Expr diffExpr = c.add({dF, c.neg(f)});
    const bool certOk =
        c.isZero(diffExpr) || c.isZero(c.expand(diffExpr)) ||
        c.isZero(c.simplify(diffExpr)) ||
        c.isZero(simplifyRationalExpr(c, diffExpr));
    if (!certOk) {
        out.reason = "mixed partial derivative certificate mismatch";
        return out;
    }

    out.F = cur;
    out.status = RationalIntegral::Status::ProvedSymbolic;
    return out;
}

DefiniteIntegral definiteIntegrateMulti(
    Ctx &c, Expr f, const std::vector<DefiniteBound> &bounds, Budget *budget)
{
    DefiniteIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (f.isNull()) {
        out.reason = "null integrand";
        return out;
    }
    if (bounds.empty()) {
        out.reason = "empty bounds list";
        return out;
    }
    for (const DefiniteBound &bnd : bounds) {
        if (bnd.var.isNull() || c.kind(bnd.var) != NodeKind::Symbol ||
            bnd.a.isNull() || bnd.b.isNull()) {
            out.reason = "invalid definite integration bound";
            return out;
        }
    }

    Expr cur = f;
    Expr lastF;
    for (const DefiniteBound &bnd : bounds) {
        const DefiniteIntegral step =
            definiteIntegrate(c, cur, bnd.var, bnd.a, bnd.b, budget);
        if (!step.proved())
            return step;
        cur = c.simplify(step.value);
        lastF = step.F;
    }

    out.value = cur;
    out.F = lastF;
    out.status = DefiniteIntegral::Status::ProvedSymbolic;
    return out;
}

namespace {

Expr subsVectorSimultaneous(Ctx &c, Expr e, const std::vector<Expr> &vars,
                            const std::vector<Expr> &repls)
{
    if (e.isNull())
        return Expr();
    std::vector<Expr> tmps;
    tmps.reserve(vars.size());
    Expr cur = e;
    for (std::size_t i = 0; i < vars.size(); ++i) {
        const Expr tmp = c.symbol("$li_tmp_" + std::to_string(i));
        tmps.push_back(tmp);
        cur = c.subs(cur, vars[i], tmp);
    }
    for (std::size_t i = 0; i < vars.size(); ++i)
        cur = c.subs(cur, tmps[i], repls[i]);
    return cur;
}

Expr simplifySqrtOnInterval(Ctx &c, Expr speedSq, Expr t, Expr a, Expr b)
{
    const Expr simpSq = c.simplify(speedSq);
    if (simpSq.isNull())
        return Expr();
    if (c.isZero(simpSq))
        return c.zero();

    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
    Expr baseExpr = simpSq;
    Expr factored;
    if (factorExpr(c, simpSq, t, factored) && !factored.isNull())
        baseExpr = factored;

    double aVal = 0.0;
    double bVal = 0.0;
    const bool hasMid =
        c.evalDouble(a, {}, aVal) && c.evalDouble(b, {}, bVal);
    const Expr midExpr =
        c.mul({half, c.add({a, b})});

    std::vector<Expr> factors;
    if (c.kind(baseExpr) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(baseExpr); ++i)
            factors.push_back(c.child(baseExpr, i));
    } else {
        factors.push_back(baseExpr);
    }

    std::vector<Expr> outFactors;
    std::vector<Expr> remUnderSqrt;
    for (Expr fk : factors) {
        if (c.kind(fk) == NodeKind::Number) {
            const Rational &rv = c.numberValue(fk);
            if (rv.signum() > 0) {
                outFactors.push_back(sqrtExpr(c, rv));
                continue;
            }
        }
        if (c.kind(fk) == NodeKind::Pow &&
            c.kind(c.child(fk, 1)) == NodeKind::Number) {
            const Rational &re = c.numberValue(c.child(fk, 1));
            std::int64_t expInt = 0;
            if (re.den() == BigInt(1) && re.num().fitsInt64(expInt) &&
                (expInt % 2 == 0)) {
                const std::int64_t halfExp = expInt / 2;
                const Expr u = c.child(fk, 0);
                if (halfExp % 2 == 0 || c.isAssumedNonNegative(u)) {
                    outFactors.push_back(c.pow(u, c.number(halfExp)));
                    continue;
                }
                if (c.isAssumedNegative(u)) {
                    outFactors.push_back(c.pow(c.neg(u), c.number(halfExp)));
                    continue;
                }
                if (hasMid) {
                    const Expr uMid = c.subs(u, t, midExpr);
                    double uVal = 0.0;
                    if (c.evalDouble(uMid, {}, uVal)) {
                        if (uVal > 1e-12) {
                            outFactors.push_back(c.pow(u, c.number(halfExp)));
                            continue;
                        }
                        if (uVal < -1e-12) {
                            outFactors.push_back(
                                c.pow(c.neg(u), c.number(halfExp)));
                            continue;
                        }
                    }
                }
            }
        }
        remUnderSqrt.push_back(fk);
    }

    if (!remUnderSqrt.empty()) {
        const Expr rem =
            remUnderSqrt.size() == 1 ? remUnderSqrt[0] : c.mul(remUnderSqrt);
        outFactors.push_back(c.simplify(c.pow(rem, half)));
    }
    return outFactors.empty() ? c.one() : c.simplify(c.mul(outFactors));
}

} // namespace

DefiniteIntegral lineIntegralScalar(Ctx &c, Expr f,
                                    const std::vector<Expr> &vars,
                                    const std::vector<Expr> &curve, Expr t,
                                    Expr a, Expr b, Budget *budget)
{
    DefiniteIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (f.isNull() || t.isNull() || c.kind(t) != NodeKind::Symbol ||
        a.isNull() || b.isNull()) {
        out.reason = "null argument in lineIntegralScalar";
        return out;
    }
    if (vars.empty() || vars.size() != curve.size()) {
        out.reason = "vars and curve dimensions must match and be non-empty";
        return out;
    }

    std::vector<Expr> sqTerms;
    sqTerms.reserve(curve.size());
    for (std::size_t i = 0; i < curve.size(); ++i) {
        if (vars[i].isNull() || c.kind(vars[i]) != NodeKind::Symbol ||
            curve[i].isNull()) {
            out.reason = "invalid variable or curve component";
            return out;
        }
        const Expr dr = c.diff(curve[i], t);
        if (dr.isNull()) {
            out.reason = "failed to differentiate curve component";
            return out;
        }
        sqTerms.push_back(c.pow(dr, c.number(std::int64_t{2})));
    }

    const Expr speedSq = c.add(sqTerms);
    const Expr ds = simplifySqrtOnInterval(c, speedSq, t, a, b);
    if (ds.isNull()) {
        out.reason = "failed to form arc-length element";
        return out;
    }

    const Expr fOnCurve = subsVectorSimultaneous(c, f, vars, curve);
    const Expr integrand = c.simplify(c.mul({fOnCurve, ds}));
    double aVal = 0.0;
    double bVal = 0.0;
    const bool reversedOrient =
        c.evalDouble(a, {}, aVal) && c.evalDouble(b, {}, bVal) && bVal < aVal;
    const Expr lo = reversedOrient ? b : a;
    const Expr hi = reversedOrient ? a : b;
    return definiteIntegrate(c, integrand, t, lo, hi, budget);
}

DefiniteIntegral lineIntegralVector(Ctx &c, const std::vector<Expr> &field,
                                    const std::vector<Expr> &vars,
                                    const std::vector<Expr> &curve, Expr t,
                                    Expr a, Expr b, Budget *budget)
{
    DefiniteIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (t.isNull() || c.kind(t) != NodeKind::Symbol || a.isNull() ||
        b.isNull()) {
        out.reason = "null argument in lineIntegralVector";
        return out;
    }
    if (vars.empty() || field.size() != vars.size() ||
        curve.size() != vars.size()) {
        out.reason =
            "field, vars, and curve dimensions must match and be non-empty";
        return out;
    }

    std::vector<Expr> dotTerms;
    dotTerms.reserve(vars.size());
    for (std::size_t i = 0; i < vars.size(); ++i) {
        if (field[i].isNull() || vars[i].isNull() ||
            c.kind(vars[i]) != NodeKind::Symbol || curve[i].isNull()) {
            out.reason = "invalid field, variable, or curve component";
            return out;
        }
        const Expr dr = c.diff(curve[i], t);
        if (dr.isNull()) {
            out.reason = "failed to differentiate curve component";
            return out;
        }
        const Expr fiOnCurve = subsVectorSimultaneous(c, field[i], vars, curve);
        dotTerms.push_back(c.mul({fiOnCurve, dr}));
    }

    const Expr integrand = c.simplify(c.add(dotTerms));
    const DefiniteIntegral direct =
        definiteIntegrate(c, integrand, t, a, b, budget);
    if (direct.proved() ||
        direct.status == DefiniteIntegral::Status::Divergent) {
        return direct;
    }

    // Fallback: Fundamental Theorem of Line Integrals when F = nabla(phi)
    const PotentialResult pot = scalarPotential(c, field, vars, budget);
    if (pot.proved() && !pot.phi.isNull()) {
        const Expr phiT =
            c.simplify(subsVectorSimultaneous(c, pot.phi, vars, curve));
        const LimitResult limB = limit(c, phiT, t, b, budget);
        const LimitResult limA = limit(c, phiT, t, a, budget);
        if (limB.proved() && limA.proved()) {
            out.F = phiT;
            out.value = c.simplify(c.add({limB.value, c.neg(limA.value)}));
            out.status = DefiniteIntegral::Status::ProvedSymbolic;
            return out;
        }
    }

    return direct;
}

namespace {

bool computeSurfaceNormal(Ctx &c, const std::vector<Expr> &surface, Expr u,
                          Expr v, std::vector<Expr> &normalOut)
{
    if (surface.size() != 3 || u.isNull() || v.isNull() ||
        c.kind(u) != NodeKind::Symbol || c.kind(v) != NodeKind::Symbol) {
        return false;
    }
    std::vector<Expr> ru(3), rv(3);
    for (std::size_t i = 0; i < 3; ++i) {
        if (surface[i].isNull())
            return false;
        ru[i] = c.diff(surface[i], u);
        rv[i] = c.diff(surface[i], v);
        if (ru[i].isNull() || rv[i].isNull())
            return false;
    }
    normalOut.resize(3);
    normalOut[0] = c.simplify(
        c.add({c.mul({ru[1], rv[2]}), c.neg(c.mul({ru[2], rv[1]}))}));
    normalOut[1] = c.simplify(
        c.add({c.mul({ru[2], rv[0]}), c.neg(c.mul({ru[0], rv[2]}))}));
    normalOut[2] = c.simplify(
        c.add({c.mul({ru[0], rv[1]}), c.neg(c.mul({ru[1], rv[0]}))}));
    return true;
}

Expr simplifySqrtMultiOnBounds(Ctx &c, Expr sqExpr,
                               const std::vector<DefiniteBound> &bounds)
{
    const Expr simpSq = c.simplify(sqExpr);
    if (simpSq.isNull())
        return Expr();
    if (c.isZero(simpSq))
        return c.zero();

    const Expr half = c.number(Rational(std::int64_t{1}, BigInt(2)));
    Expr baseExpr = simpSq;
    for (const DefiniteBound &bnd : bounds) {
        Expr factored;
        if (!bnd.var.isNull() && factorExpr(c, baseExpr, bnd.var, factored) &&
            !factored.isNull()) {
            baseExpr = factored;
        }
    }

    // Build interior midpoint substitutions from outermost bound to innermost.
    std::vector<Expr> bVars;
    std::vector<Expr> bMids;
    bVars.reserve(bounds.size());
    bMids.reserve(bounds.size());
    for (std::size_t idx = bounds.size(); idx > 0; --idx) {
        const DefiniteBound &bnd = bounds[idx - 1];
        Expr aSub = bnd.a;
        Expr bSub = bnd.b;
        if (!bVars.empty()) {
            aSub = subsVectorSimultaneous(c, aSub, bVars, bMids);
            bSub = subsVectorSimultaneous(c, bSub, bVars, bMids);
        }
        bVars.push_back(bnd.var);
        bMids.push_back(c.simplify(c.mul({half, c.add({aSub, bSub})})));
    }

    std::vector<Expr> factors;
    if (c.kind(baseExpr) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(baseExpr); ++i)
            factors.push_back(c.child(baseExpr, i));
    } else {
        factors.push_back(baseExpr);
    }

    std::vector<Expr> outFactors;
    std::vector<Expr> remUnderSqrt;
    Rational posNumFactor(std::int64_t{1});
    for (Expr fk : factors) {
        if (c.kind(fk) == NodeKind::Number) {
            const Rational &rv = c.numberValue(fk);
            if (rv.signum() > 0) {
                posNumFactor = posNumFactor * rv;
                continue;
            }
        }
        if (c.kind(fk) == NodeKind::Pow &&
            c.kind(c.child(fk, 1)) == NodeKind::Number) {
            const Rational &re = c.numberValue(c.child(fk, 1));
            std::int64_t expInt = 0;
            if (re.den() == BigInt(1) && re.num().fitsInt64(expInt) &&
                (expInt % 2 == 0)) {
                const std::int64_t halfExp = expInt / 2;
                const Expr u = c.child(fk, 0);
                if (halfExp % 2 == 0 || c.isAssumedNonNegative(u)) {
                    outFactors.push_back(c.pow(u, c.number(halfExp)));
                    continue;
                }
                if (c.isAssumedNegative(u)) {
                    outFactors.push_back(c.pow(c.neg(u), c.number(halfExp)));
                    continue;
                }
                const Expr uMid =
                    c.simplify(subsVectorSimultaneous(c, u, bVars, bMids));
                if (c.isAssumedNonNegative(uMid)) {
                    outFactors.push_back(c.pow(u, c.number(halfExp)));
                    continue;
                }
                if (c.isAssumedNegative(uMid)) {
                    outFactors.push_back(c.pow(c.neg(u), c.number(halfExp)));
                    continue;
                }
                double uVal = 0.0;
                if (c.evalDouble(uMid, {}, uVal)) {
                    if (uVal > 1e-12) {
                        outFactors.push_back(c.pow(u, c.number(halfExp)));
                        continue;
                    }
                    if (uVal < -1e-12) {
                        outFactors.push_back(
                            c.pow(c.neg(u), c.number(halfExp)));
                        continue;
                    }
                }
            }
        }
        remUnderSqrt.push_back(fk);
    }

    if (!remUnderSqrt.empty()) {
        if (!(posNumFactor == Rational(std::int64_t{1})))
            remUnderSqrt.push_back(c.number(posNumFactor));
        const Expr rem = c.expand(
            remUnderSqrt.size() == 1 ? remUnderSqrt[0] : c.mul(remUnderSqrt));
        outFactors.push_back(c.simplify(c.pow(rem, half)));
    } else if (!(posNumFactor == Rational(std::int64_t{1}))) {
        outFactors.push_back(sqrtExpr(c, posNumFactor));
    }
    return outFactors.empty() ? c.one() : c.simplify(c.mul(outFactors));
}

DefiniteBound orientPositiveBound(Ctx &c, const DefiniteBound &bnd)
{
    double aVal = 0.0, bVal = 0.0;
    if (c.evalDouble(bnd.a, {}, aVal) && c.evalDouble(bnd.b, {}, bVal) &&
        bVal < aVal) {
        return DefiniteBound{bnd.var, bnd.b, bnd.a};
    }
    return bnd;
}

bool exprEqualSymbolic(Ctx &c, Expr a, Expr b)
{
    if (a.isNull() || b.isNull())
        return false;
    const Expr diff = c.add({a, c.neg(b)});
    return c.isZero(diff) || c.isZero(c.expand(diff)) ||
           c.isZero(c.simplify(diff)) ||
           c.isZero(c.simplify(c.expand(diff))) ||
           c.isZero(simplifyRationalExpr(c, diff));
}

} // namespace

DefiniteIntegral surfaceIntegralScalar(Ctx &c, Expr f,
                                       const std::vector<Expr> &vars,
                                       const std::vector<Expr> &surface,
                                       const DefiniteBound &uBound,
                                       const DefiniteBound &vBound,
                                       Budget *budget)
{
    DefiniteIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (f.isNull() || vars.size() != 3 || surface.size() != 3) {
        out.reason =
            "surfaceIntegralScalar requires 3 spatial variables and 3 surface components";
        return out;
    }
    for (std::size_t i = 0; i < 3; ++i) {
        if (vars[i].isNull() || c.kind(vars[i]) != NodeKind::Symbol ||
            surface[i].isNull()) {
            out.reason = "invalid spatial variable or surface component";
            return out;
        }
    }

    std::vector<Expr> normal;
    if (!computeSurfaceNormal(c, surface, uBound.var, vBound.var, normal)) {
        out.reason = "failed to compute surface normal vector dr/du x dr/dv";
        return out;
    }

    const DefiniteBound uPos = orientPositiveBound(c, uBound);
    const DefiniteBound vPos = orientPositiveBound(c, vBound);
    const Expr normSq = c.add({c.pow(normal[0], c.number(std::int64_t{2})),
                               c.pow(normal[1], c.number(std::int64_t{2})),
                               c.pow(normal[2], c.number(std::int64_t{2}))});
    const Expr dS = simplifySqrtMultiOnBounds(c, normSq, {uPos, vPos});
    if (dS.isNull()) {
        out.reason = "failed to form surface area element dS";
        return out;
    }

    const Expr fOnSurface = subsVectorSimultaneous(c, f, vars, surface);
    const Expr integrand = c.simplify(c.mul({fOnSurface, dS}));
    return definiteIntegrateMulti(c, integrand, {uPos, vPos}, budget);
}

DefiniteIntegral surfaceIntegralVector(Ctx &c, const std::vector<Expr> &field,
                                       const std::vector<Expr> &vars,
                                       const std::vector<Expr> &surface,
                                       const DefiniteBound &uBound,
                                       const DefiniteBound &vBound,
                                       Budget *budget)
{
    DefiniteIntegral out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (field.size() != 3 || vars.size() != 3 || surface.size() != 3) {
        out.reason =
            "surfaceIntegralVector requires 3D field, 3 spatial variables, and 3 surface components";
        return out;
    }
    for (std::size_t i = 0; i < 3; ++i) {
        if (field[i].isNull() || vars[i].isNull() ||
            c.kind(vars[i]) != NodeKind::Symbol || surface[i].isNull()) {
            out.reason = "invalid field, spatial variable, or surface component";
            return out;
        }
    }

    std::vector<Expr> normal;
    if (!computeSurfaceNormal(c, surface, uBound.var, vBound.var, normal)) {
        out.reason = "failed to compute surface normal vector dr/du x dr/dv";
        return out;
    }

    std::vector<Expr> dotTerms;
    dotTerms.reserve(3);
    for (std::size_t i = 0; i < 3; ++i) {
        const Expr fiOnSurf =
            subsVectorSimultaneous(c, field[i], vars, surface);
        dotTerms.push_back(c.mul({fiOnSurf, normal[i]}));
    }
    const Expr integrand = c.simplify(c.add(dotTerms));
    return definiteIntegrateMulti(c, integrand, {uBound, vBound}, budget);
}

IntegralTheoremResult verifyGreenTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<ParametricCurveSegment> &boundaryCurves,
    const std::vector<DefiniteBound> &domainBounds, Budget *budget)
{
    IntegralTheoremResult out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (field.size() != 2 || vars.size() != 2 || domainBounds.size() != 2 ||
        boundaryCurves.empty()) {
        out.reason =
            "verifyGreenTheorem requires 2D field, 2 variables, non-empty boundary, and 2 domain bounds";
        return out;
    }
    if (field[0].isNull() || field[1].isNull() || vars[0].isNull() ||
        vars[1].isNull() || c.kind(vars[0]) != NodeKind::Symbol ||
        c.kind(vars[1]) != NodeKind::Symbol) {
        out.reason = "invalid field or variable in verifyGreenTheorem";
        return out;
    }

    std::vector<Expr> lhsParts;
    lhsParts.reserve(boundaryCurves.size());
    for (const ParametricCurveSegment &seg : boundaryCurves) {
        const DefiniteIntegral segInt = lineIntegralVector(
            c, field, vars, seg.curve, seg.t, seg.a, seg.b, budget);
        if (!segInt.proved()) {
            out.reason = segInt.reason.empty()
                             ? "failed to evaluate boundary line integral"
                             : segInt.reason;
            return out;
        }
        lhsParts.push_back(segInt.value);
    }
    out.lhs = c.simplify(c.add(lhsParts));

    const Expr dQdx = c.diff(field[1], vars[0]);
    const Expr dPdy = c.diff(field[0], vars[1]);
    const Expr rot2D = c.simplify(c.add({dQdx, c.neg(dPdy)}));
    const DefiniteIntegral rhsInt =
        definiteIntegrateMulti(c, rot2D, domainBounds, budget);
    if (!rhsInt.proved()) {
        out.reason = rhsInt.reason.empty()
                         ? "failed to evaluate 2D area integral of dQ/dx - dP/dy"
                         : rhsInt.reason;
        return out;
    }
    out.rhs = c.simplify(rhsInt.value);
    out.proved = exprEqualSymbolic(c, out.lhs, out.rhs);
    if (!out.proved)
        out.reason = "Green's theorem boundary and area integrals do not match";
    return out;
}

IntegralTheoremResult verifyStokesTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<ParametricCurveSegment> &boundaryCurves,
    const std::vector<Expr> &surface, const DefiniteBound &uBound,
    const DefiniteBound &vBound, Budget *budget)
{
    IntegralTheoremResult out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (field.size() != 3 || vars.size() != 3 || surface.size() != 3 ||
        boundaryCurves.empty()) {
        out.reason =
            "verifyStokesTheorem requires 3D field, 3 variables, non-empty boundary, and 3D surface";
        return out;
    }

    std::vector<Expr> lhsParts;
    lhsParts.reserve(boundaryCurves.size());
    for (const ParametricCurveSegment &seg : boundaryCurves) {
        const DefiniteIntegral segInt = lineIntegralVector(
            c, field, vars, seg.curve, seg.t, seg.a, seg.b, budget);
        if (!segInt.proved()) {
            out.reason = segInt.reason.empty()
                             ? "failed to evaluate boundary circulation integral"
                             : segInt.reason;
            return out;
        }
        lhsParts.push_back(segInt.value);
    }
    out.lhs = c.simplify(c.add(lhsParts));

    const SymMatrix curlMat = curl(c, field, vars);
    if (curlMat.rows() != 3 || curlMat.cols() != 1) {
        out.reason = "failed to compute curl(F)";
        return out;
    }
    const DefiniteIntegral rhsInt = surfaceIntegralVector(
        c, curlMat.data(), vars, surface, uBound, vBound, budget);
    if (!rhsInt.proved()) {
        out.reason = rhsInt.reason.empty()
                         ? "failed to evaluate surface flux of curl(F)"
                         : rhsInt.reason;
        return out;
    }
    out.rhs = c.simplify(rhsInt.value);
    out.proved = exprEqualSymbolic(c, out.lhs, out.rhs);
    if (!out.proved)
        out.reason = "Stokes' theorem circulation and curl-flux integrals do not match";
    return out;
}

IntegralTheoremResult verifyGaussDivergenceTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<ParametricSurfacePatch> &boundaryPatches,
    const std::vector<DefiniteBound> &volumeBounds, Budget *budget)
{
    return verifyGaussDivergenceTheorem(c, field, vars, boundaryPatches, vars,
                                        volumeBounds, budget);
}

IntegralTheoremResult verifyGaussDivergenceTheorem(
    Ctx &c, const std::vector<Expr> &field, const std::vector<Expr> &vars,
    const std::vector<ParametricSurfacePatch> &boundaryPatches,
    const std::vector<Expr> &volumeMap,
    const std::vector<DefiniteBound> &volumeBounds, Budget *budget)
{
    IntegralTheoremResult out;
    if (!checkBudget(c, budget, out.reason))
        return out;
    if (field.size() != 3 || vars.size() != 3 || boundaryPatches.empty() ||
        volumeMap.size() != 3 || volumeBounds.size() != 3) {
        out.reason =
            "verifyGaussDivergenceTheorem requires 3D field, 3 variables, non-empty boundary patches, and 3 volume bounds";
        return out;
    }

    std::vector<Expr> lhsParts;
    lhsParts.reserve(boundaryPatches.size());
    for (const ParametricSurfacePatch &patch : boundaryPatches) {
        const DefiniteIntegral patchInt = surfaceIntegralVector(
            c, field, vars, patch.surface, patch.uBound, patch.vBound, budget);
        if (!patchInt.proved()) {
            out.reason = patchInt.reason.empty()
                             ? "failed to evaluate boundary flux integral"
                             : patchInt.reason;
            return out;
        }
        lhsParts.push_back(patchInt.value);
    }
    out.lhs = c.simplify(c.add(lhsParts));

    const Expr divF = divergence(c, field, vars);
    if (divF.isNull()) {
        out.reason = "failed to compute divergence(F)";
        return out;
    }

    bool identityMap = true;
    for (std::size_t i = 0; i < 3; ++i) {
        if (!(volumeMap[i] == vars[i])) {
            identityMap = false;
            break;
        }
    }

    Expr volIntegrand = divF;
    if (!identityMap) {
        std::vector<Expr> paramVars{volumeBounds[0].var, volumeBounds[1].var,
                                    volumeBounds[2].var};
        const SymMatrix J = jacobian(c, volumeMap, paramVars);
        const Expr detJ = c.simplify(det(c, J, budget));
        const Expr detJAbs = simplifySqrtMultiOnBounds(
            c, c.pow(detJ, c.number(std::int64_t{2})), volumeBounds);
        const Expr divSub = subsVectorSimultaneous(c, divF, vars, volumeMap);
        volIntegrand = c.simplify(c.mul({divSub, detJAbs}));
    }

    const DefiniteIntegral rhsInt =
        definiteIntegrateMulti(c, volIntegrand, volumeBounds, budget);
    if (!rhsInt.proved()) {
        out.reason = rhsInt.reason.empty()
                         ? "failed to evaluate 3D volume integral of divergence(F)"
                         : rhsInt.reason;
        return out;
    }
    out.rhs = c.simplify(rhsInt.value);
    out.proved = exprEqualSymbolic(c, out.lhs, out.rhs);
    if (!out.proved)
        out.reason = "Gauss's theorem boundary flux and volume divergence integrals do not match";
    return out;
}

} // namespace numkit::cas
