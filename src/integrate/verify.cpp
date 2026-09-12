// integrate/verify.cpp — Tier-2a certified interval evaluation.
#include <numkit/cas/integrate/verify.hpp>

#include <numkit/cas/poly/sturm.hpp>
#include <numkit/cas/poly/upoly.hpp>

#include <array>
#include <cstdint>
#include <unordered_map>
#include <cassert>

namespace numkit::cas {
namespace {

// Certified rational enclosure [lo, hi], lo <= hi, outward semantics.
struct RIval
{
    Rational lo, hi;
};

const Rational &rmin(const Rational &a, const Rational &b)
{
    return a < b ? a : b;
}

const Rational &rmax(const Rational &a, const Rational &b)
{
    return a < b ? b : a;
}

RIval iAdd(const RIval &a, const RIval &b)
{
    return {a.lo + b.lo, a.hi + b.hi};
}

RIval iMul(const RIval &a, const RIval &b)
{
    const Rational l1 = a.lo * b.lo, l2 = a.lo * b.hi, l3 = a.hi * b.lo,
                  l4 = a.hi * b.hi;
    return {rmin(rmin(l1, l2), rmin(l3, l4)),
            rmax(rmax(l1, l2), rmax(l3, l4))};
}

bool containsZero(const RIval &a)
{
    return a.lo <= Rational(std::int64_t{0}) && a.hi >= Rational(std::int64_t{0});
}

RIval iDiv(const RIval &a, const RIval &b)
{
    assert(!containsZero(b));
    return iMul(a, RIval{Rational(std::int64_t{1}) / b.hi,
                         Rational(std::int64_t{1}) / b.lo});
}

RIval iPowInt(const RIval &a, std::int64_t n)
{
    if (n == 0)
        return {Rational(std::int64_t{1}), Rational(std::int64_t{1})};
    RIval r = a;
    const std::int64_t mag = n < 0 ? -n : n;
    for (std::int64_t i = 1; i < mag; ++i)
        r = iMul(r, a);
    if (n > 0)
        return r;
    return iDiv({Rational(std::int64_t{1}), Rational(std::int64_t{1})}, r);
}

// q-th root of a NON-NEGATIVE rational by bisection; the returned
// enclosure satisfies lo^q <= r <= hi^q.
RIval qRoot(const Rational &r, std::int64_t q)
{
    assert(q >= 2);
    assert(r >= Rational(std::int64_t{0}));
    const Rational one(1);
    Rational lo(0), hi = r < one ? one : r;
    const std::uint64_t qe = static_cast<std::uint64_t>(q);
    // 24 bisection steps: width <= max(1, r)/2^24 - far finer than
    // any genuine value difference the check needs to separate
    // (real form bugs differ by >= 2x, not in the 7th decimal).
    for (int i = 0; i < 24; ++i) {
        const Rational mid = (lo + hi) * Rational(std::int64_t{1}, BigInt(2));
        // mid^q <= r  <=>  mid.num^q * r.den^q <= r.num * mid.den^q
        if (BigInt::powUInt(mid.num(), qe) * BigInt::powUInt(r.den(), qe) <=
            r.num() * BigInt::powUInt(mid.den(), qe))
            lo = mid;
        else
            hi = mid;
    }
    return {lo, hi};
}

// (p/q)-th power of a non-negative interval (x^(p/q) is monotone
// on x >= 0; a zero lower end with positive p stays zero).
RIval iPowRatPos(const RIval &a, std::int64_t p, std::int64_t q)
{
    const std::uint64_t pe = static_cast<std::uint64_t>(p < 0 ? -p : p);
    const bool zeroLo = a.lo == Rational(std::int64_t{0});
    const RIval rl = zeroLo ? RIval{Rational(0), Rational(0)} : qRoot(a.lo, q);
    const RIval rh = qRoot(a.hi, q);
    auto fracPow = [](const Rational &x, std::uint64_t e) {
        return Rational(BigInt::powUInt(x.num(), e),
                        BigInt::powUInt(x.den(), e));
    };
    RIval base{fracPow(rl.lo, pe), fracPow(rh.hi, pe)};
    if (p >= 0)
        return base;
    return iDiv({Rational(std::int64_t{1}), Rational(std::int64_t{1})}, base);
}

// Per-check cache: the SAME RootOf atom appears many times in a form
// (in N2, in the atan argument, in log arguments) and across the
// sample points; refine once. SUCCESSFUL enclosures only - a failed
// lookup (complex root) must keep failing, never turn into a
// cached [0,0] that would silently null the whole form.
using RootOfCache = std::unordered_map<std::uint32_t, RIval>;

bool evalRootOf(const Ctx &c, Expr e, RootOfCache &cache, RIval &out)
{
    const auto hit = cache.find(c.id(e));
    if (hit != cache.end()) {
        out = hit->second;
        return true;
    }
    const std::vector<Rational> &poly = c.rootOfPoly(e);
    const int index = c.rootOfIndex(e);
    UPoly p = UPoly(poly).squarefreePart();
    p.makeMonic();
    const std::vector<RootInterval> ivs = isolateRealRoots(p);
    if (index < 0 || index >= static_cast<int>(ivs.size()))
        return false; // complex root or out of range: Unknown
        // (deliberately NOT cached: the enclosing evalIval fails the
        // whole sample, and a cached failure marker would later read
        // as a success with a bogus value)
    // 2^-24 refinement: mismatch detection only needs to separate
    // values that genuinely differ (real form bugs are >= 2x
    // coefficient errors); polynomial-cascade overestimation stays
    // orders of magnitude below any true difference.
    const RootInterval iv =
        refineRoot(p, ivs[static_cast<std::size_t>(index)],
                   Rational(std::int64_t{1}, BigInt(1) << 24));
    out = {iv.lo, iv.hi};
    cache.emplace(c.id(e), out);
    return true;
}

// Enclosure of e at x = x0; false = a subtree outside the algebraic
// fragment (free symbol, Func, unsupported exponent shape) - the
// caller counts the point as unusable, never as failure.
bool evalIval(const Ctx &c, Expr e, Expr var, const Rational &x0,
              RootOfCache &cache, RIval &out)
{
    switch (c.kind(e)) {
    case NodeKind::Number:
        out = {c.numberValue(e), c.numberValue(e)};
        return true;
    case NodeKind::Symbol:
        if (!(e == var))
            return false;
        out = {x0, x0};
        return true;
    case NodeKind::RootOf:
        return evalRootOf(c, e, cache, out);
    case NodeKind::Pow: {
        RIval base;
        if (!evalIval(c, c.child(e, 0), var, x0, cache, base))
            return false;
        if (c.kind(c.child(e, 1)) != NodeKind::Number)
            return false;
        const Rational &v = c.numberValue(c.child(e, 1));
        std::int64_t p = 0;
        if (v.den() == BigInt(1) && v.num().fitsInt64(p)) {
            if (p < 0 && containsZero(base))
                return false;
            out = iPowInt(base, p);
            return true;
        }
        std::int64_t q = 0;
        if (!v.den().fitsInt64(q) || q <= 0 || !v.num().fitsInt64(p))
            return false;
        if (base.lo < Rational(std::int64_t{0}) ||
            (base.lo == Rational(std::int64_t{0}) && p < 0))
            return false; // fractional power needs x >= 0 here
        out = iPowRatPos(base, p, q);
        return true;
    }
    case NodeKind::Add:
    case NodeKind::Mul: {
        const bool isAdd = c.kind(e) == NodeKind::Add;
        RIval acc = isAdd ? RIval{Rational(std::int64_t{0}),
                                  Rational(std::int64_t{0})}
                          : RIval{Rational(std::int64_t{1}),
                                  Rational(std::int64_t{1})};
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            RIval v;
            if (!evalIval(c, c.child(e, i), var, x0, cache, v))
                return false;
            acc = isAdd ? iAdd(acc, v) : iMul(acc, v);
        }
        out = acc;
        return true;
    }
    default:
        return false;
    }
}

bool disjoint(const RIval &a, const RIval &b)
{
    return a.hi < b.lo || b.hi < a.lo;
}

} // namespace

Tier2aStatus tier2aFormCheck(Ctx &c, Expr F, Expr f, Expr var)
{
    if (F.isNull())
        return Tier2aStatus::Unknown;
    const Expr dF = c.diff(F, var);

    // Positive rational sample points. Poles of rational integrands
    // are algebraic numbers, so small positive rationals are almost
    // always pole-free; every unusable point (zero-crossing divisor,
    // fractional power of a negative, complex RootOf) just reduces
    // the compatible count - it can never turn into Mismatch.
    const std::array<Rational, 6> kSamples = {{
        Rational(std::int64_t{1}, BigInt(2)),
        Rational(std::int64_t{5}, BigInt(4)),
        Rational(std::int64_t{3}, BigInt(2)),
        Rational(std::int64_t{3}),
        Rational(std::int64_t{17}, BigInt(6)),
        Rational(std::int64_t{9}, BigInt(2)),
    }};

    RootOfCache cache;
    int compatible = 0;
    for (const Rational &x0 : kSamples) {
        RIval a, b;
        if (!evalIval(c, dF, var, x0, cache, a) ||
            !evalIval(c, f, var, x0, cache, b))
            continue;
        if (disjoint(a, b))
            // Proven: the form's derivative differs from the
            // integrand at x0. Overestimation only ever widens
            // enclosures, so disjoint is CERTIFIED.
            return Tier2aStatus::Mismatch;
        ++compatible;
    }
    return compatible >= 3 ? Tier2aStatus::Match : Tier2aStatus::Unknown;
}

} // namespace numkit::cas
