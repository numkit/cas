#include <numkit/cas/integrate/ratint.hpp>

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

UPoly pmod(const UPoly &a, const UPoly &b)
{
    UPoly q, r;
    UPoly::divMod(a, b, q, r);
    return r;
}

// Inverse of u modulo m (gcd(u, m) = 1), via extended Euclid.
UPoly invMod(const UPoly &u, const UPoly &m)
{
    assert(!m.isZero());
    UPoly r0 = m, r1 = pmod(u, m);
    UPoly s0, s1(R1());
    while (!r1.isZero()) {
        UPoly q, r;
        UPoly::divMod(r0, r1, q, r);
        UPoly s2 = s0 - q * s1;
        r0 = r1;
        r1 = r;
        s0 = s1;
        s1 = s2;
    }
    assert(r0.isConst());
    return s0 * (R1() / r0.lc());
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
        const UPoly inv = invMod(pmod(prod, Ps[idx]), Ps[idx]);
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

// Integrate A/F (F squarefree) into pieces; false with a reason when
// F has a factor outside the M0 splitting scope.
bool integrateSquarefree(const UPoly &A, const UPoly &F,
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

} // namespace

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
                                     invMod(pmod(coef, F), F),
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
    for (std::size_t i = 0; i < sq.size(); ++i) {
        if (gs[i].isZero())
            continue;
        if (!integrateSquarefree(gs[i], sq[i], pieces, out.reason))
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
    out.F = c.add(terms);
    out.status = RationalIntegral::Status::ProvedSymbolic;
    out.reason.clear();
    return out;
}

} // namespace numkit::cas
