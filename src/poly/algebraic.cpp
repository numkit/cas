#include <keel/core.h>
#include <numkit/cas/poly/algebraic.hpp>

#include <cassert>

namespace numkit::cas {

namespace {

const Rational R0()
{
    return Rational(keel::i64{0});
}

const Rational R1()
{
    return Rational(keel::i64{1});
}

UPoly linearOf(const Rational &r)
{
    return UPoly(keel::Array<Rational>{Rational(-r), R1()});
}

keel::i32 cmpRational(const Rational &a, const Rational &b)
{
    return a < b ? -1 : (b < a ? 1 : 0);
}

} // namespace

Algebraic::Algebraic()
{
    poly_ = linearOf(R0());
    iv_ = RootInterval{R0(), R0()};
}

Algebraic::Algebraic(Rational r)
{
    poly_ = linearOf(r);
    iv_ = RootInterval{r, r};
}

Algebraic::Algebraic(UPoly p, RootInterval iv)
{
    assert(!p.isZero() && p.deg() >= 1);
    assert(UPoly::gcd(p, p.derivative()).isConst() &&
           "defining polynomial must be squarefree");
    // Rationals normalize to the canonical linear form.
    if (iv.exact()) {
        assert(p.eval(iv.lo).isZero());
        poly_ = linearOf(iv.lo);
        iv_ = RootInterval{iv.lo, iv.lo};
        return;
    }
    if (p.deg() == 1) {
        const Rational r = R0() - p.coeff(0) / p.lc();
        poly_ = linearOf(r);
        iv_ = RootInterval{r, r};
        return;
    }
    p.makeMonic();
    poly_ = keel::move(p);
    iv_ = iv;
}

keel::Array<Algebraic> Algebraic::realRoots(const UPoly &p)
{
    const UPoly psf = p.squarefreePart();
    keel::Array<Algebraic> out;
    if (psf.isConst())
        return out;
    for (const RootInterval &iv : isolateRealRoots(p))
        out.emplace_back(psf, iv);
    return out;
}

Rational Algebraic::rationalValue() const
{
    assert(isRational());
    return R0() - poly_.coeff(0);
}

// True iff a's number is a root of g. Any root of g lying strictly
// inside a's open isolating interval is a root of a's own polynomial
// there, hence is a's number itself.
bool Algebraic::containsRoot(const UPoly &g, keel::ArrayRef<UPoly> sturmG,
                             const Algebraic &a)
{
    if (a.isRational())
        return g.eval(a.rationalValue()).isZero();
    keel::usize n = countRealRoots(sturmG, a.iv_.lo, a.iv_.hi); // (lo, hi]
    if (g.eval(a.iv_.hi).isZero())
        --n; // a root at hi is not the number (open interval)
    return n > 0;
}

// Interval position: -1/+1 when separated, 0 when undecided.
keel::i32 Algebraic::positionCompare(const Algebraic &other) const
{
    const RootInterval &A = iv_;
    const RootInterval &B = other.iv_;
    if (A.exact() && B.exact())
        return cmpRational(A.lo, B.lo);
    if (A.exact()) {
        if (A.lo <= B.lo)
            return -1; // B's open root is strictly right of B.lo >= A.lo
        if (B.hi <= A.lo)
            return 1;
        return 0; // strictly inside B's interval
    }
    if (B.exact())
        return -other.positionCompare(*this);
    if (A.hi <= B.lo)
        return -1;
    if (B.hi <= A.lo)
        return 1;
    return 0;
}

void Algebraic::refineStep()
{
    if (iv_.exact())
        return;
    const Rational width = (iv_.hi - iv_.lo) * Rational(keel::i64{1}, BigInt(2));
    const RootInterval next = refineRoot(poly_, iv_, width);
    if (next.exact()) {
        // Bisection landed on the root exactly: it is rational.
        const Rational r = next.lo;
        poly_ = linearOf(r);
        iv_ = RootInterval{r, r};
        return;
    }
    iv_ = next;
}

keel::i32 Algebraic::sign() const
{
    if (isRational())
        return rationalValue().signum();
    while (true) {
        if (iv_.lo.signum() > 0)
            return 1;
        if (iv_.hi.signum() < 0)
            return -1;
        if (iv_.lo.signum() == 0)
            return 1; // 0 is the open left endpoint: root strictly right
        if (iv_.hi.signum() == 0)
            return -1; // 0 is the open right endpoint: root strictly left
        if (poly_.eval(R0()).isZero())
            return 0; // 0 strictly inside and a root: it is the number
        const_cast<Algebraic *>(this)->refineStep();
    }
}

keel::i32 Algebraic::compare(const Algebraic &a, const Algebraic &b)
{
    if (a.isRational() && b.isRational())
        return cmpRational(a.rationalValue(), b.rationalValue());

    Algebraic x = a, y = b;
    bool samePoly = false;
    const UPoly g = UPoly::gcd(a.poly_, b.poly_);
    if (!g.isConst()) {
        const keel::Array<UPoly> sturmG = sturmSequence(g);
        // A common root of both polynomials is a root of g. If both
        // numbers live among g's roots, comparing roots of one
        // polynomial decides everything; otherwise they are distinct.
        if (containsRoot(g, sturmG, a) && containsRoot(g, sturmG, b)) {
            x.poly_ = g;
            y.poly_ = g;
            samePoly = true;
        }
    }
    const keel::Array<UPoly> sturmW =
        samePoly ? sturmSequence(g) : keel::Array<UPoly>();

    while (true) {
        const keel::i32 pos = x.positionCompare(y);
        if (pos != 0)
            return pos;

        if (x.iv_.exact() && !y.iv_.exact()) {
            // Rational strictly inside y's interval: equal iff it is a
            // root of y's polynomial; else refine y until separated.
            if (y.poly_.eval(x.iv_.lo).isZero())
                return 0;
            while (true) {
                y.refineStep();
                const keel::i32 p2 = x.positionCompare(y);
                if (p2 != 0)
                    return p2;
            }
        }
        if (y.iv_.exact() && !x.iv_.exact())
            return -compare(y, x);

        if (samePoly) {
            // Both open, overlapping: one root of the common polynomial
            // strictly inside the intersection means it is both numbers.
            const Rational lo = x.iv_.lo > y.iv_.lo ? x.iv_.lo : y.iv_.lo;
            const Rational hi = x.iv_.hi < y.iv_.hi ? x.iv_.hi : y.iv_.hi;
            keel::usize n = countRealRoots(sturmW, lo, hi); // (lo, hi]
            if (g.eval(hi).isZero())
                --n;
            if (n == 1)
                return 0;
        }
        // Distinct (or not yet equal-decided): refine apart. Distinctness
        // was proven when !samePoly, and the samePoly branch detects the
        // shared root, so both loops terminate.
        x.refineStep();
        y.refineStep();
    }
}

void Algebraic::refineTo(const Rational &width)
{
    if (iv_.exact())
        return;
    const RootInterval next = refineRoot(poly_, iv_, width);
    if (next.exact()) {
        const Rational r = next.lo;
        poly_ = linearOf(r);
        iv_ = RootInterval{r, r};
        return;
    }
    iv_ = next;
}

keel::f64 Algebraic::approx() const
{
    if (iv_.exact())
        return iv_.lo.toDouble();
    const_cast<Algebraic *>(this)->refineTo(
        Rational(keel::i64{1}, BigInt(1000000)));
    const keel::f64 lo = iv_.lo.toDouble();
    const keel::f64 hi = iv_.hi.toDouble();
    return 0.5 * (lo + hi);
}

} // namespace numkit::cas
