#include <numkit/cas/poly/sturm.hpp>

#include <algorithm>
#include <cassert>
#include <deque>

namespace numkit::cas {

std::vector<UPoly> sturmSequence(const UPoly &p)
{
    std::vector<UPoly> s;
    if (p.isZero() || p.deg() < 1)
        return s;
    s.push_back(p);
    UPoly cur = p.derivative();
    if (cur.isZero())
        return s;
    s.push_back(cur);
    while (true) {
        UPoly q, r;
        UPoly::divMod(s[s.size() - 2], s[s.size() - 1], q, r);
        if (r.isZero())
            break;
        s.push_back(-r);
    }
    return s;
}

Rational cauchyRootBound(const UPoly &p)
{
    assert(!p.isZero());
    const Rational an = p.lc().abs();
    Rational m(0);
    for (std::size_t i = 0; i + 1 < p.coeffs().size(); ++i)
        if (p.coeff(i).abs() > m)
            m = p.coeff(i).abs();
    return Rational(std::int64_t{1}) + m / an;
}

namespace {

int signOfR(const Rational &r)
{
    return r.signum();
}

// Sign variations of the Sturm chain at x (zeros skipped).
std::size_t variations(const std::vector<UPoly> &sturm, const Rational &x)
{
    std::size_t v = 0;
    int prev = 0;
    for (const UPoly &s : sturm) {
        const int sg = signOfR(s.eval(x));
        if (sg == 0)
            continue;
        if (prev != 0 && sg != prev)
            ++v;
        prev = sg;
    }
    return v;
}

} // namespace

std::size_t countRealRoots(const std::vector<UPoly> &sturm,
                           const Rational &a, const Rational &b)
{
    assert(!sturm.empty());
    assert(a < b);
    return variations(sturm, a) - variations(sturm, b);
}

std::vector<RootInterval> isolateRealRoots(const UPoly &p0)
{
    std::vector<RootInterval> out;
    if (p0.isZero())
        return out;
    const UPoly p = p0.squarefreePart();
    if (p.isConst())
        return out;

    const std::vector<UPoly> sturm = sturmSequence(p);
    const Rational B = cauchyRootBound(p);

    // Work items carry (lo, hi, rootAtHi): count(lo, hi) has (lo, hi]
    // semantics, so an interval whose right endpoint is an already
    // recorded exact root must subtract it. The left endpoint is never
    // a root: (a, b] excludes a.
    struct Item
    {
        Rational lo, hi;
        bool rootAtHi;
    };
    std::deque<Item> work;
    work.push_back({-B, B, false});
    while (!work.empty()) {
        const Item it = work.front();
        work.pop_front();
        const std::size_t n =
            countRealRoots(sturm, it.lo, it.hi) - (it.rootAtHi ? 1 : 0);
        if (n == 0)
            continue;
        if (n == 1) {
            out.push_back(RootInterval{it.lo, it.hi});
            continue;
        }
        const Rational mid = (it.lo + it.hi) * Rational(std::int64_t{1}, BigInt(2));
        if (p.eval(mid).isZero()) {
            out.push_back(RootInterval{mid, mid});
            work.push_back({it.lo, mid, true});
            work.push_back({mid, it.hi, it.rootAtHi});
        } else {
            work.push_back({it.lo, mid, false});
            work.push_back({mid, it.hi, it.rootAtHi});
        }
    }

    std::sort(out.begin(), out.end(),
              [](const RootInterval &a, const RootInterval &b) {
                  return a.lo < b.lo;
              });
    return out;
}

RootInterval refineRoot(const UPoly &p, RootInterval iv,
                        const Rational &targetWidth)
{
    if (iv.exact())
        return iv;
    // Endpoints of an isolated interval may themselves be recorded exact
    // roots; the (a, b] Sturm count excludes a, so half selection by
    // counting stays correct with root endpoints.
    const std::vector<UPoly> sturm = sturmSequence(p);
    while (iv.hi - iv.lo > targetWidth) {
        const Rational mid = (iv.lo + iv.hi) * Rational(std::int64_t{1}, BigInt(2));
        if (p.eval(mid).isZero())
            return RootInterval{mid, mid};
        if (countRealRoots(sturm, iv.lo, mid) > 0)
            iv.hi = mid;
        else
            iv.lo = mid;
    }
    return iv;
}

} // namespace numkit::cas
