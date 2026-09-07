#include <numkit/cas/poly/fppoly.hpp>

#include <algorithm>
#include <cassert>

namespace numkit::cas {

namespace {

std::uint64_t addMod(std::uint64_t a, std::uint64_t b, std::uint64_t p)
{
    const std::uint64_t s = a + b;
    return s >= p ? s - p : s;
}

std::uint64_t subMod(std::uint64_t a, std::uint64_t b, std::uint64_t p)
{
    return a >= b ? a - b : a + p - b;
}

std::uint64_t mulMod(std::uint64_t a, std::uint64_t b, std::uint64_t p)
{
    return (a * b) % p;
}

// Deterministic PRNG for Cantor-Zassenhaus (fixed seed per call chain).
std::uint64_t fpNext(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

} // namespace

void FpPoly::checkSameField(const FpPoly &a, const FpPoly &b)
{
    assert((!a.hasP() || !b.hasP() || a.p_ == b.p_) && "FpPoly field mismatch");
}

FpPoly FpPoly::derivative() const
{
    FpPoly out;
    out.p_ = p_;
    if (c_.size() <= 1)
        return out;
    for (std::size_t i = 1; i < c_.size(); ++i)
        out.c_.push_back(mulMod(c_[i], i % p_, p_));
    out.trim();
    return out;
}

FpPoly::FpPoly(std::uint64_t p, std::vector<std::uint64_t> coeffs)
    : p_(p), c_(std::move(coeffs))
{
    assert(p >= 3 && p < (std::uint64_t{1} << 31));
    for (std::uint64_t &c : c_)
        c %= p;
    trim();
}

void FpPoly::trim()
{
    while (!c_.empty() && c_.back() == 0)
        c_.pop_back();
}

FpPoly FpPoly::constant(std::uint64_t p, std::uint64_t c)
{
    return FpPoly(p, std::vector<std::uint64_t>{c});
}

FpPoly FpPoly::monomial(std::uint64_t p, std::uint64_t c, std::size_t exp)
{
    std::vector<std::uint64_t> cs(exp + 1, 0);
    cs[exp] = c % p;
    return FpPoly(p, std::move(cs));
}

FpPoly FpPoly::x(std::uint64_t p)
{
    return monomial(p, 1, 1);
}

std::uint64_t FpPoly::lc() const
{
    assert(!isZero());
    return c_.back();
}

FpPoly operator+(const FpPoly &a, const FpPoly &b)
{
    FpPoly::checkSameField(a, b);
    const std::uint64_t p = a.hasP() ? a.p_ : b.p_;
    FpPoly out;
    out.p_ = p;
    out.c_.reserve(std::max(a.c_.size(), b.c_.size()));
    for (std::size_t i = 0; i < std::max(a.c_.size(), b.c_.size()); ++i)
        out.c_.push_back(addMod(a.coeff(i), b.coeff(i), p));
    out.trim();
    return out;
}

FpPoly operator-(const FpPoly &a, const FpPoly &b)
{
    FpPoly::checkSameField(a, b);
    const std::uint64_t p = a.hasP() ? a.p_ : b.p_;
    FpPoly out;
    out.p_ = p;
    out.c_.reserve(std::max(a.c_.size(), b.c_.size()));
    for (std::size_t i = 0; i < std::max(a.c_.size(), b.c_.size()); ++i)
        out.c_.push_back(subMod(a.coeff(i), b.coeff(i), p));
    out.trim();
    return out;
}

FpPoly FpPoly::operator-() const
{
    FpPoly out;
    out.p_ = p_;
    out.c_.reserve(c_.size());
    for (std::uint64_t v : c_)
        out.c_.push_back(v == 0 ? 0 : p_ - v);
    return out;
}

FpPoly operator*(const FpPoly &a, const FpPoly &b)
{
    FpPoly::checkSameField(a, b);
    if (a.isZero() || b.isZero())
        return FpPoly();
    const std::uint64_t p = a.p_;
    FpPoly out;
    out.p_ = p;
    out.c_.assign(a.c_.size() + b.c_.size() - 1, 0);
    for (std::size_t i = 0; i < a.c_.size(); ++i)
        for (std::size_t j = 0; j < b.c_.size(); ++j) {
            const std::uint64_t v = mulMod(a.c_[i], b.c_[j], p);
            out.c_[i + j] = addMod(out.c_[i + j], v, p);
        }
    out.trim();
    return out;
}

FpPoly FpPoly::operator*(std::uint64_t k) const
{
    FpPoly out;
    out.p_ = p_;
    out.c_.reserve(c_.size());
    const std::uint64_t kk = k % p_;
    for (std::uint64_t v : c_)
        out.c_.push_back(mulMod(v, kk, p_));
    out.trim();
    return out;
}

std::uint64_t FpPoly::invModP(std::uint64_t a, std::uint64_t p)
{
    assert(a % p != 0);
    std::int64_t t = 0, newt = 1;
    std::int64_t r = static_cast<std::int64_t>(p), newr = static_cast<std::int64_t>(a % p);
    while (newr != 0) {
        const std::int64_t q = r / newr;
        std::int64_t tmp = t - q * newt;
        t = newt;
        newt = tmp;
        tmp = r - q * newr;
        r = newr;
        newr = tmp;
    }
    assert(r == 1 && "inverse of a non-invertible element");
    std::int64_t result = t;
    if (result < 0)
        result += static_cast<std::int64_t>(p);
    return static_cast<std::uint64_t>(result);
}

void FpPoly::divMod(const FpPoly &a, const FpPoly &b, FpPoly &q, FpPoly &r)
{
    FpPoly::checkSameField(a, b);
    assert(!b.isZero() && b.hasP());
    const std::uint64_t p = b.p_;
    r = a;
    r.p_ = p;
    q = FpPoly();
    q.p_ = p;
    if (a.isZero() || a.deg() < b.deg())
        return;
    q.c_.assign(static_cast<std::size_t>(a.deg() - b.deg()) + 1, 0);
    const std::uint64_t blcInv = invModP(b.lc(), p);
    while (!r.isZero() && r.deg() >= b.deg()) {
        const int shift = r.deg() - b.deg();
        const std::uint64_t f = mulMod(r.lc(), blcInv, p);
        q.c_[static_cast<std::size_t>(shift)] = addMod(q.c_[static_cast<std::size_t>(shift)], f, p);
        for (std::size_t j = 0; j < b.c_.size(); ++j)
            r.c_[j + static_cast<std::size_t>(shift)] =
                subMod(r.c_[j + static_cast<std::size_t>(shift)], mulMod(f, b.c_[j], p), p);
        r.trim();
    }
}

FpPoly operator%(const FpPoly &a, const FpPoly &b)
{
    FpPoly q, r;
    FpPoly::divMod(a, b, q, r);
    return r;
}

FpPoly FpPoly::gcd(const FpPoly &a, const FpPoly &b)
{
    FpPoly::checkSameField(a, b);
    const std::uint64_t p = a.hasP() ? a.p_ : b.p_;
    FpPoly x = a, y = b;
    x.p_ = p;
    y.p_ = p;
    while (!y.isZero()) {
        FpPoly q, r;
        divMod(x, y, q, r);
        x = y;
        y = r;
    }
    if (!x.isZero())
        x = x * invModP(x.lc(), p);
    return x;
}

FpPoly FpPoly::powMod(const BigInt &e, const FpPoly &m) const
{
    assert(!m.isZero() && m.hasP());
    FpPoly result = constant(m.p_, 1);
    FpPoly base = *this;
    base.p_ = m.p_;
    base = base % m;
    BigInt n = e;
    while (n.signum() > 0) {
        BigInt q2, r2;
        BigInt::divMod(n, BigInt(2), q2, r2);
        if (!r2.isZero())
            result = (result * base) % m;
        base = (base * base) % m;
        n = q2;
    }
    return result;
}

std::uint64_t FpPoly::eval(std::uint64_t x0) const
{
    std::uint64_t acc = 0;
    for (std::size_t i = c_.size(); i-- > 0;)
        acc = addMod(mulMod(acc, x0 % p_, p_), c_[i], p_);
    return acc;
}

bool operator==(const FpPoly &a, const FpPoly &b)
{
    if (a.isZero() || b.isZero())
        return a.c_.empty() && b.c_.empty();
    return a.p_ == b.p_ && a.c_ == b.c_;
}

bool operator!=(const FpPoly &a, const FpPoly &b)
{
    return !(a == b);
}

// ── factorization ──────────────────────────────────────────────

namespace {

// Cantor-Zassenhaus equal-degree splitting: all irreducible factors of
// g have degree d. Deterministic via the fixed-seed PRNG.
void edf(const FpPoly &g, int d, std::vector<FpPoly> &out, std::uint64_t &rng)
{
    assert(!g.isZero());
    if (g.deg() < d) {
        out.push_back(g);
        return;
    }
    if (g.deg() == d) {
        out.push_back(g);
        return;
    }
    const std::uint64_t p = g.p();
    while (true) {
        // random poly of degree < deg(g), not constant
        const int degA = 1 + static_cast<int>(fpNext(rng) % static_cast<std::uint64_t>(g.deg()));
        std::vector<std::uint64_t> cs;
        for (int i = 0; i <= degA; ++i)
            cs.push_back(fpNext(rng) % p);
        const FpPoly a(p, cs);
        if (a.isZero() || a.deg() == 0)
            continue;
        // exponent (p^d - 1)/2
        BigInt e = BigInt::powUInt(BigInt(p), static_cast<std::uint64_t>(d));
        e = (e - BigInt(1)) >> 1;
        const FpPoly b = a.powMod(e, g);
        const FpPoly h = FpPoly::gcd(b - FpPoly::constant(p, 1), g);
        if (!h.isZero() && h.deg() > 0 && h.deg() < g.deg()) {
            FpPoly q, r;
            FpPoly::divMod(g, h, q, r);
            assert(r.isZero());
            edf(h, d, out, rng);
            edf(q, d, out, rng);
            return;
        }
    }
}

} // namespace

std::vector<FpPoly> FpPoly::factor(const FpPoly &f)
{
    assert(f.hasP() && !f.isZero());
    const std::uint64_t p = f.p();
    std::vector<FpPoly> out;
    if (f.deg() < 1)
        return out;

    // Squarefree part: f / gcd(f, f').
    FpPoly d = f.derivative();
    FpPoly g = FpPoly::gcd(f, d);
    FpPoly sf;
    if (g.isOne() || g.isZero()) {
        sf = f;
    } else {
        FpPoly q, r;
        FpPoly::divMod(f, g, q, r);
        assert(r.isZero());
        sf = q;
    }
    if (sf.deg() < 1)
        return out;
    sf = sf * invModP(sf.lc(), p); // monic

    // Distinct-degree factorization: h tracks x^(p^k) mod sf.
    std::uint64_t rng = 0x9E3779B97F4A7C15ULL;
    FpPoly h = FpPoly::x(p) % sf;
    FpPoly rest = sf;
    int degd = 0;
    while (rest.deg() >= 1) {
        ++degd;
        h = h.powMod(BigInt(p), rest);
        FpPoly fac = FpPoly::gcd(h - FpPoly::x(p), rest);
        if (fac.deg() > 0) {
            if (fac.deg() == degd)
                out.push_back(fac);
            else
                edf(fac, degd, out, rng);
            FpPoly q, r;
            FpPoly::divMod(rest, fac, q, r);
            assert(r.isZero());
            rest = q;
            h = h % rest;
        }
        if (rest.deg() == 0)
            break;
    }
    std::sort(out.begin(), out.end(), [](const FpPoly &a, const FpPoly &b) {
        if (a.deg() != b.deg())
            return a.deg() < b.deg();
        for (std::size_t i = a.size(); i-- > 0;)
            if (a.coeff(i) != b.coeff(i))
                return a.coeff(i) < b.coeff(i);
        return false;
    });
    return out;
}

bool FpPoly::isIrreducible() const
{
    if (deg() < 1)
        return false;
    FpPoly m = *this;
    if (m.lc() != 1)
        m = m * invModP(m.lc(), p_);
    // x^(p^d) == x (mod g)?
    const BigInt pd = BigInt::powUInt(BigInt(p_), static_cast<std::uint64_t>(deg()));
    const FpPoly h = FpPoly::x(p_).powMod(pd, m);
    if ((h - FpPoly::x(p_)) % m != FpPoly())
        return false;
    // gcd(x^(p^(d/q)) - x, g) == 1 for each prime q | d.
    int dd = deg();
    for (int q = 2; q * q <= dd; ++q) {
        if (dd % q != 0)
            continue;
        while (dd % q == 0)
            dd /= q;
        const BigInt pk = BigInt::powUInt(BigInt(p_), static_cast<std::uint64_t>(deg() / q));
        const FpPoly hq = FpPoly::x(p_).powMod(pk, m);
        if (!(FpPoly::gcd(hq - FpPoly::x(p_), m)).isOne())
            return false;
    }
    if (dd > 1) {
        const BigInt pk = BigInt::powUInt(BigInt(p_), static_cast<std::uint64_t>(deg() / dd));
        const FpPoly hq = FpPoly::x(p_).powMod(pk, m);
        if (!(FpPoly::gcd(hq - FpPoly::x(p_), m)).isOne())
            return false;
    }
    return true;
}

} // namespace numkit::cas
