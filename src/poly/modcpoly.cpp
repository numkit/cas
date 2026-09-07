#include <numkit/cas/poly/modcpoly.hpp>

#include <algorithm>
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

} // namespace

void ModCPoly::checkSameRing(const ModCPoly &a, const ModCPoly &b)
{
    assert((!a.hasRing() || !b.hasRing() || a.ring_ == b.ring_) &&
           "ModCPoly operands from different rings");
}

// ── ModCRing ───────────────────────────────────────────────────

ModCRing::ModCRing(UPoly c)
{
    assert(!c.isZero() && c.deg() >= 1);
    c.makeMonic();
    c_ = std::move(c);
    zero_ = UPoly();
    one_ = UPoly(R1());
}

UPoly ModCRing::add(const UPoly &a, const UPoly &b) const
{
    return reduce(a + b);
}

UPoly ModCRing::sub(const UPoly &a, const UPoly &b) const
{
    return reduce(a - b);
}

UPoly ModCRing::neg(const UPoly &a) const
{
    return -a;
}

UPoly ModCRing::mul(const UPoly &a, const UPoly &b) const
{
    if (c_.deg() == 2) {
        // Closed form for the quadratic modulus t^2 = -p*t - q: no
        // division-based reduction inside the hot Euclidean loops
        // (thousands of ring multiplications per gcd, each formerly
        // paying a full polynomial division in reduce()).
        assert(a.deg() < 2 && b.deg() < 2 && "ring element out of normal form");
        const Rational &p = c_.coeff(1);
        const Rational &q = c_.coeff(0);
        const Rational &a0 = a.coeff(0);
        const Rational a1 = a.coeff(1);
        const Rational &b0 = b.coeff(0);
        const Rational b1 = b.coeff(1);
        const Rational t2 = a1 * b1; // coefficient of t^2 before reduction
        const Rational m0 = a0 * b0 - q * t2;
        const Rational m1 = a0 * b1 + a1 * b0 - p * t2;
        return UPoly(std::vector<Rational>{m0, m1});
    }
    if (c_.deg() == 3) {
        // Closed form for the cubic modulus t^3 = -k2*t^2 - k1*t - k0
        // (same rationale as the quadratic case: the RootOf branch's
        // per-point loops pay thousands of ring multiplications, and
        // reduce() is a division there).
        assert(a.deg() < 3 && b.deg() < 3 && "ring element out of normal form");
        const Rational &k2 = c_.coeff(2);
        const Rational &k1 = c_.coeff(1);
        const Rational &k0 = c_.coeff(0);
        const Rational a0 = a.coeff(0), a1 = a.coeff(1), a2 = a.coeff(2);
        const Rational b0 = b.coeff(0), b1 = b.coeff(1), b2 = b.coeff(2);
        const Rational p0 = a0 * b0;
        const Rational p1 = a0 * b1 + a1 * b0;
        const Rational p2 = a0 * b2 + a1 * b1 + a2 * b0;
        const Rational p3 = a1 * b2 + a2 * b1;
        const Rational p4 = a2 * b2;
        // t^4 = t*t^3 -> (k2^2 - k1)t^2 + (k2*k1 - k0)t + k2*k0
        const Rational m0 = p0 - k0 * p3 + k0 * k2 * p4;
        const Rational m1 = p1 - k1 * p3 + (k2 * k1 - k0) * p4;
        const Rational m2 = p2 - k2 * p3 + (k2 * k2 - k1) * p4;
        return UPoly(std::vector<Rational>{m0, m1, m2});
    }
    return reduce(a * b);
}

UPoly ModCRing::div(const UPoly &a, const UPoly &b) const
{
    return mul(a, inv(b));
}

UPoly ModCRing::inv(const UPoly &a) const
{
    assert(!a.isZero());
    if (c_.deg() == 2) {
        // Quadratic conjugate t -> -p - t: (a0 + a1*t) * conj(a) is
        // the rational norm N = a0^2 - p*a0*a1 + q*a1^2, nonzero for
        // a != 0 because c is irreducible (the ring is a field), so
        // the inverse is conj(a)/N — no extended Euclid.
        assert(a.deg() < 2 && "ring element out of normal form");
        const Rational &p = c_.coeff(1);
        const Rational &q = c_.coeff(0);
        const Rational &a0 = a.coeff(0);
        const Rational a1 = a.coeff(1);
        const Rational n = a0 * a0 - p * a0 * a1 + q * a1 * a1;
        assert(!n.isZero() && "nonzero element has zero norm: c reducible?");
        const Rational i0 = (a0 - p * a1) / n;
        const Rational i1 = Rational(std::int64_t{-1}) * a1 / n;
        return UPoly(std::vector<Rational>{i0, i1});
    }
    return UPoly::invMod(a, c_);
}

bool ModCRing::isOne(const UPoly &a) const
{
    return a == one_;
}

// ── ModCPoly ───────────────────────────────────────────────────

const ModCRing &ModCPoly::ring() const
{
    assert(ring_ != nullptr);
    return *ring_;
}

void ModCPoly::trim()
{
    while (!c_.empty() && c_.back().isZero())
        c_.pop_back();
}

ModCPoly::ModCPoly(const ModCRing &ring, std::vector<UPoly> coeffs)
    : ring_(&ring), c_(std::move(coeffs))
{
    for (UPoly &c : c_) {
        assert(c.deg() < ring_->modulus().deg() && "unreduced coefficient");
        c = ring_->reduce(c);
    }
    trim();
}

ModCPoly ModCPoly::constant(const ModCRing &ring, UPoly c0)
{
    return ModCPoly(ring, std::vector<UPoly>{std::move(c0)});
}

ModCPoly ModCPoly::monomial(const ModCRing &ring, UPoly c0, std::size_t exp)
{
    std::vector<UPoly> cs(exp + 1, ring.zero());
    cs[exp] = std::move(c0);
    return ModCPoly(ring, std::move(cs));
}

const UPoly &ModCPoly::lc() const
{
    assert(!isZero());
    return c_.back();
}

ModCPoly operator+(const ModCPoly &a, const ModCPoly &b)
{
    ModCPoly::checkSameRing(a, b);
    const ModCRing *rg = a.hasRing() ? a.ring_ : b.ring_;
    assert(rg != nullptr);
    std::vector<UPoly> cs;
    cs.reserve(std::max(a.c_.size(), b.c_.size()));
    for (std::size_t i = 0; i < std::max(a.c_.size(), b.c_.size()); ++i)
        cs.push_back(rg->add(a.coeff(i), b.coeff(i)));
    return ModCPoly(*rg, std::move(cs));
}

ModCPoly operator-(const ModCPoly &a, const ModCPoly &b)
{
    ModCPoly::checkSameRing(a, b);
    const ModCRing *rg = a.hasRing() ? a.ring_ : b.ring_;
    assert(rg != nullptr);
    std::vector<UPoly> cs;
    cs.reserve(std::max(a.c_.size(), b.c_.size()));
    for (std::size_t i = 0; i < std::max(a.c_.size(), b.c_.size()); ++i)
        cs.push_back(rg->sub(a.coeff(i), b.coeff(i)));
    return ModCPoly(*rg, std::move(cs));
}

ModCPoly ModCPoly::operator-() const
{
    if (!hasRing())
        return *this;
    ModCPoly out;
    out.ring_ = ring_;
    out.c_.reserve(c_.size());
    for (const UPoly &c : c_)
        out.c_.push_back(ring_->neg(c));
    return out;
}

ModCPoly operator*(const ModCPoly &a, const ModCPoly &b)
{
    ModCPoly::checkSameRing(a, b);
    if (a.isZero() || b.isZero())
        return ModCPoly();
    const ModCRing &r = a.ring();
    std::vector<UPoly> cs(a.c_.size() + b.c_.size() - 1, r.zero());
    for (std::size_t i = 0; i < a.c_.size(); ++i)
        for (std::size_t j = 0; j < b.c_.size(); ++j)
            cs[i + j] = r.add(cs[i + j], r.mul(a.c_[i], b.c_[j]));
    return ModCPoly(r, std::move(cs));
}

void ModCPoly::divMod(const ModCPoly &a, const ModCPoly &b,
                      ModCPoly &q, ModCPoly &r)
{
    ModCPoly::checkSameRing(a, b);
    assert(!b.isZero() && b.hasRing());
    const ModCRing &ring = b.ring();
    r = a;
    q = ModCPoly();
    q.ring_ = &ring;
    if (a.isZero() || a.deg() < b.deg())
        return;
    q.c_.assign(static_cast<std::size_t>(a.deg() - b.deg()) + 1, ring.zero());
    const UPoly blcInv = ring.inv(b.lc());
    while (!r.isZero() && r.deg() >= b.deg()) {
        const int shift = r.deg() - b.deg();
        const UPoly f = ring.mul(r.lc(), blcInv);
        q.c_[static_cast<std::size_t>(shift)] = ring.add(q.c_[static_cast<std::size_t>(shift)], f);
        for (std::size_t j = 0; j < b.c_.size(); ++j)
            r.c_[j + static_cast<std::size_t>(shift)] =
                ring.sub(r.c_[j + static_cast<std::size_t>(shift)],
                         ring.mul(f, b.c_[j]));
        r.trim();
    }
}

void ModCPoly::makeMonic()
{
    assert(!isZero());
    const UPoly k = ring_->inv(lc());
    for (UPoly &c : c_)
        c = ring_->mul(c, k);
}

ModCPoly ModCPoly::gcd(const ModCPoly &a, const ModCPoly &b)
{
    // Monic Euclidean loop, same rationale as UPoly::gcd: normalizing
    // every remainder keeps the ring-coefficient fractions at
    // polynomial growth (the raw loop let them explode - the second
    // divMod alone cost 3x the first on the profile task).
    ModCPoly::checkSameRing(a, b);
    ModCPoly x = a, y = b;
    if (!y.isZero())
        y.makeMonic();
    while (!y.isZero()) {
        ModCPoly q, r;
        divMod(x, y, q, r);
        x = y;
        y = r;
        if (!y.isZero())
            y.makeMonic();
    }
    if (!x.isZero())
        x.makeMonic();
    return x;
}

bool operator==(const ModCPoly &a, const ModCPoly &b)
{
    if (a.isZero() || b.isZero())
        return a.c_.empty() && b.c_.empty();
    ModCPoly::checkSameRing(a, b);
    return a.c_ == b.c_;
}

bool operator!=(const ModCPoly &a, const ModCPoly &b)
{
    return !(a == b);
}

std::string ModCPoly::toString() const
{
    std::string out;
    for (const UPoly &c : c_) {
        if (!out.empty())
            out += "|";
        bool first = true;
        for (const Rational &q : c.coeffs()) {
            if (!first)
                out += ",";
            out += q.toString();
            first = false;
        }
    }
    return out;
}

} // namespace numkit::cas
