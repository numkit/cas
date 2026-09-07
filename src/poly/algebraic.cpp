#include <numkit/cas/poly/algebraic.hpp>

#include <cassert>
#include <string>

namespace numkit::cas {

namespace {

const Rational R0()
{
    return Rational(std::int64_t{0});
}

const Rational R1()
{
    return Rational(std::int64_t{1});
}

UPoly linearOf(const Rational &r)
{
    return UPoly(std::vector<Rational>{Rational(-r), R1()});
}

int cmpRational(const Rational &a, const Rational &b)
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
    poly_ = std::move(p);
    iv_ = iv;
}

std::vector<Algebraic> Algebraic::realRoots(const UPoly &p)
{
    const UPoly psf = p.squarefreePart();
    std::vector<Algebraic> out;
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
bool Algebraic::containsRoot(const UPoly &g, const std::vector<UPoly> &sturmG,
                             const Algebraic &a)
{
    if (a.isRational())
        return g.eval(a.rationalValue()).isZero();
    std::size_t n = countRealRoots(sturmG, a.iv_.lo, a.iv_.hi); // (lo, hi]
    if (g.eval(a.iv_.hi).isZero())
        --n; // a root at hi is not the number (open interval)
    return n > 0;
}

// Interval position: -1/+1 when separated, 0 when undecided.
int Algebraic::positionCompare(const Algebraic &other) const
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
    const Rational width = (iv_.hi - iv_.lo) * Rational(std::int64_t{1}, BigInt(2));
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

int Algebraic::sign() const
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

int Algebraic::compare(const Algebraic &a, const Algebraic &b)
{
    if (a.isRational() && b.isRational())
        return cmpRational(a.rationalValue(), b.rationalValue());

    Algebraic x = a, y = b;
    bool samePoly = false;
    const UPoly g = UPoly::gcd(a.poly_, b.poly_);
    if (!g.isConst()) {
        const std::vector<UPoly> sturmG = sturmSequence(g);
        // A common root of both polynomials is a root of g. If both
        // numbers live among g's roots, comparing roots of one
        // polynomial decides everything; otherwise they are distinct.
        if (containsRoot(g, sturmG, a) && containsRoot(g, sturmG, b)) {
            x.poly_ = g;
            y.poly_ = g;
            samePoly = true;
        }
    }
    const std::vector<UPoly> sturmW =
        samePoly ? sturmSequence(g) : std::vector<UPoly>();

    while (true) {
        const int pos = x.positionCompare(y);
        if (pos != 0)
            return pos;

        if (x.iv_.exact() && !y.iv_.exact()) {
            // Rational strictly inside y's interval: equal iff it is a
            // root of y's polynomial; else refine y until separated.
            if (y.poly_.eval(x.iv_.lo).isZero())
                return 0;
            while (true) {
                y.refineStep();
                const int p2 = x.positionCompare(y);
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
            std::size_t n = countRealRoots(sturmW, lo, hi); // (lo, hi]
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

double Algebraic::approx() const
{
    if (iv_.exact())
        return std::stod(iv_.lo.num().toString()) /
               std::stod(iv_.lo.den().toString());
    const_cast<Algebraic *>(this)->refineTo(
        Rational(std::int64_t{1}, BigInt(1000000)));
    const double lo = std::stod(iv_.lo.num().toString()) /
                      std::stod(iv_.lo.den().toString());
    const double hi = std::stod(iv_.hi.num().toString()) /
                      std::stod(iv_.hi.den().toString());
    return 0.5 * (lo + hi);
}

} // namespace numkit::cas
