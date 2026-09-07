#include <numkit/cas/poly/zassenhaus.hpp>

#include <numkit/cas/poly/fppoly.hpp>

#include <algorithm>
#include <cassert>

namespace numkit::cas {

namespace {

const BigInt B0()
{
    return BigInt(0);
}

const BigInt B1()
{
    return BigInt(1);
}

// ── integer-polynomial helpers (ascending BigInt vectors) ─────

void bpTrim(std::vector<BigInt> &a)
{
    while (!a.empty() && a.back().isZero())
        a.pop_back();
}

std::vector<BigInt> bpMul(const std::vector<BigInt> &a, const std::vector<BigInt> &b)
{
    if (a.empty() || b.empty())
        return {};
    std::vector<BigInt> out(a.size() + b.size() - 1, B0());
    for (std::size_t i = 0; i < a.size(); ++i)
        for (std::size_t j = 0; j < b.size(); ++j)
            out[i + j] = out[i + j] + a[i] * b[j];
    bpTrim(out);
    return out;
}

std::vector<BigInt> bpSub(const std::vector<BigInt> &a, const std::vector<BigInt> &b)
{
    std::vector<BigInt> out(std::max(a.size(), b.size()), B0());
    for (std::size_t i = 0; i < a.size(); ++i)
        out[i] = a[i];
    for (std::size_t i = 0; i < b.size(); ++i)
        out[i] = out[i] - b[i];
    bpTrim(out);
    return out;
}

// Canonical non-negative residues: BigInt::divMod is TRUNCATED, so a
// negative coefficient leaves a negative remainder — lift it back into
// [0, m). Consumers feed possibly-negative symmetric values through
// here (Hensel state, reconstruction candidates).
void bpMod(std::vector<BigInt> &a, const BigInt &m)
{
    for (BigInt &c : a) {
        BigInt q, r;
        BigInt::divMod(c, m, q, r);
        if (r.isNegative())
            r = r + m;
        c = r;
    }
}

// c mod p as a uint64 in [0, p) — BigInt divMod is TRUNCATED, so
// negative inputs leave a negative remainder that must be corrected.
std::uint64_t modP(const BigInt &c, std::uint64_t p)
{
    BigInt q, r;
    BigInt::divMod(c, BigInt(p), q, r);
    if (r.isNegative())
        r = r + BigInt(p);
    return r.isZero() ? 0 : static_cast<std::uint64_t>(r.lowLimb());
}

FpPoly toFp(const std::vector<BigInt> &a, std::uint64_t p)
{
    std::vector<std::uint64_t> cs;
    for (const BigInt &c : a)
        cs.push_back(modP(c, p));
    return FpPoly(p, cs);
}

std::vector<BigInt> fromFp(const FpPoly &a, std::uint64_t p)
{
    std::vector<BigInt> out;
    for (std::uint64_t c : a.coeffsAll())
        out.push_back(BigInt(c));
    return out;
}

// Exact division over Z: true iff b divides a exactly (including
// leading-coefficient divisibility); q receives the quotient.
bool bpDivExact(const std::vector<BigInt> &a, const std::vector<BigInt> &b,
                std::vector<BigInt> &q)
{
    if (b.empty())
        return false;
    if (a.empty()) {
        q = {};
        return true;
    }
    if (a.size() < b.size())
        return false;
    std::vector<BigInt> r = a;
    q.assign(a.size() - b.size() + 1, B0());
    const int db = static_cast<int>(b.size()) - 1;
    while (!r.empty()) {
        const int dr = static_cast<int>(r.size()) - 1;
        const int shift = dr - db;
        if (shift < 0)
            return false;
        BigInt quo, rem;
        BigInt::divMod(r[dr], b[db], quo, rem);
        if (!rem.isZero())
            return false;
        q[static_cast<std::size_t>(shift)] = quo;
        for (std::size_t j = 0; j < b.size(); ++j)
            r[j + static_cast<std::size_t>(shift)] =
                r[j + static_cast<std::size_t>(shift)] - quo * b[j];
        bpTrim(r);
    }
    return true;
}

// Normalize to primitive part with positive leading coefficient.
void bpNormalize(std::vector<BigInt> &a)
{
    if (a.empty())
        return;
    if (a.back().isNegative())
        for (BigInt &c : a)
            c = -c;
    BigInt cont = B0();
    for (const BigInt &c : a)
        if (!c.isZero())
            cont = BigInt::gcd(cont, c);
    if (!cont.isZero() && !(cont == B1())) {
        for (BigInt &c : a) {
            BigInt q, r;
            BigInt::divMod(c, cont, q, r);
            assert(r.isZero());
            c = q;
        }
    }
    bpTrim(a);
}

// All positive divisors of n, ascending, built from the canonical
// factorization. The old trial-division enumeration walked to
// sqrt(cofactor) in BigInt steps — a ~2^40 leading coefficient with a
// large prime factor cost millions of BigInt divisions and dominated
// the whole integration; see notes/c1-algebraic-layer.md (baseline
// profiling session).
std::vector<BigInt> divisorsOf(const BigInt &n)
{
    std::vector<BigInt> divs{B1()};
    for (const auto &pe : BigInt::factorize(n)) {
        const std::size_t base = divs.size();
        BigInt pw(1);
        for (int e = 1; e <= pe.second; ++e) {
            pw = pw * pe.first;
            for (std::size_t w = 0; w < base; ++w)
                divs.push_back(divs[w] * pw);
        }
    }
    std::sort(divs.begin(), divs.end());
    return divs;
}

// Symmetric representatives in (-pk/2, pk/2].
std::vector<BigInt> bpSymmetric(const std::vector<BigInt> &a, const BigInt &pk)
{
    std::vector<BigInt> out;
    const BigInt half = pk >> 1;
    for (const BigInt &c : a) {
        BigInt v = c;
        if (half < v)
            v = v - pk;
        out.push_back(v);
    }
    bpTrim(out);
    return out;
}

// ── Hensel lifting ─────────────────────────────────────────────

// One linear step: g*h == target (mod m) becomes g'*h' == target
// (mod p*m), with the FIXED Bezout pair s*g + t*h == 1 over F_p
// (g and h stay congruent to themselves mod p during lifting, so the
// pair never changes).
void henselStep(const std::vector<BigInt> &target,
                const FpPoly &gFp, const FpPoly &hFp,
                const FpPoly &sFp, const FpPoly &tFp,
                std::uint64_t p, const BigInt &m,
                std::vector<BigInt> &g, std::vector<BigInt> &h)
{
    std::vector<BigInt> e = bpSub(target, bpMul(g, h));
    std::vector<std::uint64_t> eFpCs;
    for (const BigInt &c : e) {
        BigInt q, r;
        BigInt::divMod(c, m, q, r);
        assert(r.isZero() && "henselStep: congruence invariant broken");
        eFpCs.push_back(modP(q, p));
    }
    const FpPoly eFp(p, eFpCs);

    // g*v + h*u = e over F_p with BOTH corrections reduced:
    // u = (t*e) mod g, v = (s*e) mod h. The reduction of v modulo h is
    // what preserves deg h through the lift (from s*g + t*h = 1:
    // e - h*u = s*g*e + q*g*h for u = t*e - q*g, so (e - h*u)/g =
    // s*e + q*h which must be taken mod h).
    const FpPoly u = (tFp * eFp) % gFp;
    const FpPoly v = (sFp * eFp) % hFp;
    {
        auto fs = [](const FpPoly &q) {
            std::string o;
            for (std::uint64_t c : q.coeffsAll()) o += std::to_string(c) + " ";
            return o;
        };
    }

    const std::vector<BigInt> uZ = fromFp(u, p);
    const std::vector<BigInt> vZ = fromFp(v, p);
    const auto accumulate = [&](std::vector<BigInt> &dst, const std::vector<BigInt> &d) {
        if (dst.size() < d.size())
            dst.resize(d.size(), B0());
        for (std::size_t i = 0; i < d.size(); ++i)
            dst[i] = dst[i] + m * d[i];
        bpTrim(dst);
    };
    accumulate(g, uZ);
    accumulate(h, vZ);
}

// Lift g[lo..hi) so their product equals target (mod pk), by splitting
// off the last factor as one side of the pair.
void henselGroup(const std::vector<BigInt> &target,
                 std::vector<std::vector<BigInt>> &g,
                 std::size_t lo, std::size_t hi,
                 const std::vector<FpPoly> &gFp,
                 std::uint64_t p, const BigInt &pk)
{
    if (hi - lo <= 1)
        return;
    const std::size_t mid = hi - 1;

    std::vector<BigInt> A(g[lo]);
    for (std::size_t i = lo + 1; i < mid; ++i)
        A = bpMul(A, g[i]);

    const FpPoly aFp = toFp(A, p);
    FpPoly sFp, tFp;
    FpPoly::extGcd(aFp, gFp[mid], sFp, tFp);

    BigInt m = BigInt(p);
    std::vector<BigInt> B = g[mid];
    while (m < pk) {
        henselStep(target, aFp, gFp[mid], sFp, tFp, p, m, A, B);
        m = m * BigInt(p);
        bpMod(A, m);
        bpMod(B, m);
    }
    g[mid] = B;
    if (mid == lo + 1)
        g[lo] = A; // singleton left group: A IS the lifted factor
    henselGroup(A, g, lo, mid, gFp, p, pk);
}

// Masks over the active factor list in (popcount, value) order,
// skipping the empty and full masks.
int popcount32(std::uint32_t v)
{
    int c = 0;
    while (v) {
        v &= v - 1;
        ++c;
    }
    return c;
}

std::vector<std::uint32_t> subsetMasks(std::size_t n)
{
    std::vector<std::uint32_t> masks;
    const std::uint32_t full = (n >= 32) ? ~std::uint32_t{0}
                                         : ((std::uint32_t{1} << n) - 1);
    for (std::uint32_t m = 1; m <= full - 1 && m != 0; ++m)
        masks.push_back(m);
    std::sort(masks.begin(), masks.end(), [](std::uint32_t a, std::uint32_t b) {
        const int pa = popcount32(a), pb = popcount32(b);
        return pa != pb ? pa < pb : a < b;
    });
    return masks;
}

} // namespace

std::vector<std::vector<BigInt>> factorPrimitiveInteger(const std::vector<BigInt> &fIn)
{
    std::vector<BigInt> f = fIn;
    bpTrim(f);
    assert(!f.empty() && f.size() >= 2 && "need degree >= 1");
    // Strip the content: the caller gets the factors of the primitive
    // part (a non-unit content is the caller's business).
    bpNormalize(f);
    if (f.size() == 2)
        return {f};

    // Prime search: p must not kill the leading coefficient and f must
    // stay squarefree mod p.
    const std::uint64_t kPrimes[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43};
    std::uint64_t p = 0;
    FpPoly fFp;
    const int degF = static_cast<int>(f.size()) - 1;
    for (std::uint64_t cand : kPrimes) {
        FpPoly fp = toFp(f, cand);
        if (fp.isZero() || fp.deg() != degF) // p must not divide the lc
            continue;
        if (FpPoly::gcd(fp, fp.derivative()).deg() != 0)
            continue;
        p = cand;
        fFp = fp;
        break;
    }
    if (p == 0)
        return {f}; // no suitable small prime found: return whole

    std::vector<FpPoly> gFp = FpPoly::factor(fFp);
    const std::size_t r = gFp.size();
    if (r <= 1)
        return {f}; // irreducible mod p => irreducible over Q
    assert(r < 32 && "subset enumeration limit");
    // All gFp are MONIC: the lift runs against the monic associate of f
    // (absorbing lc mod p into a factor would freeze the product's
    // leading coefficient and break the congruence for k >= 3: the
    // corrections have degree below their factor and never touch the
    // leading coefficient). The integer leading coefficients are
    // recovered during reconstruction by trying the divisors of lc(f).

    // Mignotte bound: factor coefficients are bounded by 2^deg*||f||inf.
    // Lift until p^k exceeds that bound WITH HEADROOM: the reconstruction
    // prefilter rejects a candidate when its symmetric representative
    // escapes `bound`, and that only bites when the representative
    // range (−pk/2, pk/2] is comfortably wider than the bound — with
    // pk barely above `bound` every residue formally fits and the
    // prefilter degenerates to nothing. The extra lifting steps cost
    // logarithmically little.
    BigInt infNorm = B0();
    for (const BigInt &c : f)
        if (c.abs() > infNorm)
            infNorm = c.abs();
    const BigInt bound =
        (BigInt(1) << static_cast<std::size_t>(fFp.deg())) * infNorm * BigInt(2);
    BigInt pk = BigInt(p);
    while (pk <= bound * BigInt(32))
        pk = pk * BigInt(p);

    std::vector<std::vector<BigInt>> g;
    for (const FpPoly &gf : gFp)
        g.push_back(fromFp(gf, p));
    // monic associate of f, reduced mod pk: f/lc * (lc^-1 mod pk exists
    // because p does not divide lc). Lifting monic target with monic
    // factors is structurally consistent to any k.
    const BigInt lcF = f.back();
    BigInt lcInv, lcRem;
    // extended-gcd-free inverse: lc * lcInv = 1 mod pk via brute-free
    // Euclid on BigInt
    {
        // solve lc*lcInv + pk*y = gcd (=1) via the same loop as invModP
        BigInt t0(0), t1(1), r0(pk), r1 = (([&] {
            BigInt q2, r2;
            BigInt::divMod(lcF, pk, q2, r2);
            return r2.isZero() ? BigInt(0) : r2;
        })());
        // r1 = lcF mod pk, guaranteed nonzero
        while (!r1.isZero()) {
            BigInt q3, r3;
            BigInt::divMod(r0, r1, q3, r3);
            BigInt t2 = t0 - q3 * t1;
            r0 = r1;
            r1 = r3;
            t0 = t1;
            t1 = t2;
        }
        // r0 is gcd(lcF, pk) = 1 here (p does not divide lc)
        lcInv = t0 % pk;
        if (lcInv.isNegative())
            lcInv = lcInv + pk;
    }
    (void)lcRem;
    std::vector<BigInt> target = f;
    bpMod(target, pk);
    for (BigInt &c : target)
        c = (c * lcInv) % pk;
    henselGroup(target, g, 0, r, gFp, p, pk);

    // Reconstruction: only divisors found by exact division over Z are
    // recorded; the final leftover is the exact integer cofactor (never
    // a lifted representative, which is only defined modulo p^k).
    std::vector<std::vector<BigInt>> out;
    std::vector<std::size_t> active;
    for (std::size_t i = 0; i < r; ++i)
        active.push_back(i);
    std::vector<BigInt> cur = f;

    while (!cur.empty() && cur.size() >= 2) {
        const std::uint32_t n = static_cast<std::uint32_t>(active.size());
        bool found = false;
        if (n >= 2) {
            // Every positive divisor of the current leading coefficient
            // (NO size cap — the old 40-bit crutch silently reduced
            // {1, lc} for larger coefficients and dropped every true
            // factor, returning the polynomial whole). Computed ONCE
            // per while-iteration: `cur` only changes when a factor is
            // found, and recomputing per subset mask re-factored the
            // same lc up to 2^n times.
            const std::vector<BigInt> divs = divisorsOf(cur.back().abs());
            for (std::uint32_t mask : subsetMasks(n)) {
                std::vector<BigInt> cand{B1()};
                for (std::uint32_t i = 0; i < n; ++i)
                    if (mask & (std::uint32_t{1} << i)) {
                        cand = bpMul(cand, g[active[i]]);
                        bpMod(cand, pk);
                    }
                std::vector<BigInt> sym = bpSymmetric(cand, pk);
                if (sym.empty() || sym.size() < 2)
                    continue;
                // the true divisor is D * sym where D divides lc(cur).
                // Constant-term sieve FIRST: a true factor F divides
                // cur, so F(0) divides cur(0) whenever both are
                // nonzero; F(0) is the symmetric representative of
                // D*sym[0] mod pk, so a wrong D dies on ONE scalar
                // multiply+divide instead of scaling and reducing the
                // whole candidate polynomial. With smooth leading
                // coefficients listing tens of thousands of divisors
                // this is the difference between sieving and grinding.
                const BigInt &curConst = cur[0];
                const BigInt &sym0 = sym[0];
                const BigInt halfConst = pk >> 1;
                for (const BigInt &d : divs) {
                    if (!curConst.isZero() && !sym0.isZero()) {
                        BigInt rep0 = (d * sym0) % pk;
                        if (rep0.isNegative())
                            rep0 = rep0 + pk;
                        if (rep0 > halfConst)
                            rep0 = rep0 - pk;
                        if (rep0.abs() > bound)
                            continue;
                        BigInt q0, r0;
                        BigInt::divMod(curConst, rep0, q0, r0);
                        if (!r0.isZero())
                            continue;
                    }
                    std::vector<BigInt> scaled = sym;
                    for (BigInt &c : scaled)
                        c = c * d;
                    bpMod(scaled, pk);
                    scaled = bpSymmetric(scaled, pk);
                    // Mignotte prefilter: a true factor of f fits
                    // within `bound` coefficient-wise, and the check
                    // must happen on the REDUCED representative —
                    // D * sym as plain integers can be huge while its
                    // symmetric residue is the small true factor.
                    // Scalar comparisons here are far cheaper than
                    // the exact polynomial division below, which
                    // matters for smooth leading coefficients listing
                    // tens of thousands of divisors.
                    bool over = false;
                    for (const BigInt &c : scaled)
                        if (c.abs() > bound) {
                            over = true;
                            break;
                        }
                    if (over)
                        continue;
                    std::vector<BigInt> qv;
                    if (bpDivExact(cur, scaled, qv)) {
                        bpNormalize(scaled); // after division: before it,
                        // content-stripping destroys the D scale
                        out.push_back(scaled);
                        cur = qv;
                        std::vector<std::size_t> keep;
                        for (std::uint32_t i = 0; i < n; ++i)
                            if (!(mask & (std::uint32_t{1} << i)))
                                keep.push_back(active[i]);
                        active = keep;
                        found = true;
                        break;
                    }
                }
                if (found)
                    break;
            }
        }
        if (!found) {
            // the remaining cofactor over Z is the last irreducible
            std::vector<BigInt> sym = cur;
            bpNormalize(sym);
            if (sym.size() >= 2)
                out.push_back(sym);
            cur.clear();
            break;
        }
    }

    std::sort(out.begin(), out.end(),
              [](const std::vector<BigInt> &a, const std::vector<BigInt> &b) {
                  if (a.size() != b.size())
                      return a.size() < b.size();
                  for (std::size_t i = a.size(); i-- > 0;)
                      if (a[i] != b[i])
                          return a[i] < b[i];
                  return false;
              });
    return out;
}

std::vector<UPoly> factorOverQ(const UPoly &f)
{
    std::vector<UPoly> out;
    if (f.isZero() || f.deg() < 1)
        return out;

    // Clear denominators and strip the content.
    BigInt denLcm(1);
    for (const Rational &c : f.coeffs())
        denLcm = BigInt::lcm(denLcm, c.den());
    std::vector<BigInt> ipoly;
    for (const Rational &c : f.coeffs()) {
        BigInt q, r;
        BigInt::divMod(denLcm, c.den(), q, r);
        ipoly.push_back(c.num() * q);
    }
    bpNormalize(ipoly);
    if (ipoly.size() < 2)
        return out;

    // Multiplicity-aware: Yun's decomposition over Q, distinct factors
    // of each squarefree component, emitted with their powers.
    const std::vector<UPoly> comps = f.squarefreeDecomposition();
    for (std::size_t i = 0; i < comps.size(); ++i) {
        const UPoly &comp = comps[i];
        if (comp.isConst())
            continue;
        BigInt denLcm2(1);
        for (const Rational &c : comp.coeffs())
            denLcm2 = BigInt::lcm(denLcm2, c.den());
        std::vector<BigInt> ip2;
        for (const Rational &c : comp.coeffs()) {
            BigInt q2, r2;
            BigInt::divMod(denLcm2, c.den(), q2, r2);
            ip2.push_back(c.num() * q2);
        }
        for (const std::vector<BigInt> &g : factorPrimitiveInteger(ip2)) {
            std::vector<Rational> cs;
            const BigInt glc = g.back();
            for (const BigInt &c : g)
                cs.emplace_back(c, glc);
            const UPoly fact(cs);
            for (std::size_t k = 0; k <= i; ++k) // multiplicity i+1
                out.push_back(fact);
        }
    }
    return out;
}

} // namespace numkit::cas
