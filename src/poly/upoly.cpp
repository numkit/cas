#include <keel/core.h>
#include <keel/format.h>
#include <numkit/cas/poly/upoly.hpp>

#include <algorithm>
#include <cassert>

namespace numkit::cas {

UPoly::UPoly(Rational c)
{
    if (!c.isZero())
        c_.push_back(std::move(c));
}

UPoly::UPoly(keel::Array<Rational> coeffs) : c_(keel::move(coeffs))
{
    trim();
}

UPoly UPoly::monomial(Rational c, keel::u64 exp)
{
    UPoly out;
    if (!c.isZero()) {
        out.c_.assign(keel::as<keel::usize>(exp) + 1,
                      Rational(keel::i64{0}));
        out.c_[keel::as<keel::usize>(exp)] = std::move(c);
    }
    return out;
}

void UPoly::trim()
{
    while (!c_.empty() && c_.back().isZero())
        c_.pop_back();
}

void UPoly::makeMonic()
{
    assert(!isZero());
    const Rational inv = Rational(keel::i64{1}) / lc();
    for (Rational &c : c_)
        c *= inv;
    trim();
}

const Rational &UPoly::lc() const
{
    assert(!isZero());
    return c_.back();
}

Rational UPoly::eval(const Rational &x) const
{
    Rational acc(keel::i64{0});
    for (keel::usize i = c_.size(); i-- > 0;)
        acc = acc * x + c_[i];
    return acc;
}

UPoly operator+(const UPoly &a, const UPoly &b)
{
    UPoly out;
    out.c_.reserve(std::max(a.c_.size(), b.c_.size()));
    for (keel::usize i = 0; i < std::max(a.c_.size(), b.c_.size()); ++i)
        out.c_.push_back(a.coeff(i) + b.coeff(i));
    out.trim();
    return out;
}

UPoly operator-(const UPoly &a, const UPoly &b)
{
    UPoly out;
    out.c_.reserve(std::max(a.c_.size(), b.c_.size()));
    for (keel::usize i = 0; i < std::max(a.c_.size(), b.c_.size()); ++i)
        out.c_.push_back(a.coeff(i) - b.coeff(i));
    out.trim();
    return out;
}

UPoly UPoly::operator-() const
{
    UPoly out;
    out.c_.reserve(c_.size());
    for (const Rational &c : c_)
        out.c_.push_back(-c);
    return out;
}

UPoly operator*(const UPoly &a, const UPoly &b)
{
    if (a.isZero() || b.isZero())
        return UPoly();
    UPoly out;
    out.c_.assign(a.c_.size() + b.c_.size() - 1, Rational(keel::i64{0}));
    for (keel::usize i = 0; i < a.c_.size(); ++i)
        for (keel::usize j = 0; j < b.c_.size(); ++j)
            out.c_[i + j] += a.c_[i] * b.c_[j];
    out.trim();
    return out;
}

UPoly operator*(const UPoly &a, const Rational &k)
{
    if (k.isZero())
        return UPoly();
    UPoly out;
    out.c_.reserve(a.c_.size());
    for (const Rational &c : a.c_)
        out.c_.push_back(c * k);
    return out;
}

UPoly operator*(const Rational &k, const UPoly &a)
{
    return a * k;
}

void UPoly::divMod(const UPoly &a, const UPoly &b, UPoly &q, UPoly &r)
{
    assert(!b.isZero() && "UPoly division by zero");
    const UPoly aCopy = a;
    const UPoly bCopy = b;
    r = aCopy;
    q = UPoly();
    if (aCopy.isZero() || aCopy.deg() < bCopy.deg())
        return;
    q.c_.assign(keel::as<keel::usize>(aCopy.deg() - bCopy.deg()) + 1,
                Rational(keel::i64{0}));
    const Rational blcInv = Rational(keel::i64{1}) / bCopy.lc();
    while (!r.isZero() && r.deg() >= bCopy.deg()) {
        const keel::i32 shift = r.deg() - bCopy.deg();
        const Rational f = r.lc() * blcInv;
        q.c_[keel::as<keel::usize>(shift)] += f;
        for (keel::usize j = 0; j < bCopy.c_.size(); ++j)
            r.c_[j + keel::as<keel::usize>(shift)] -= f * bCopy.c_[j];
        r.trim();
    }
}

UPoly operator%(const UPoly &a, const UPoly &b)
{
    UPoly q, r;
    UPoly::divMod(a, b, q, r);
    return r;
}

UPoly UPoly::invMod(const UPoly &u, const UPoly &m)
{
    assert(!m.isZero());
    // Monic extended Euclid: normalizing the remainder chain keeps the
    // cofactor coefficients at polynomial growth instead of the
    // exponential blow-up of the raw PRS (the quadratic/cubic ring
    // inversions sit inside every ModCPoly division). The ideal (m)
    // is unchanged by taking the monic associate, and each
    // normalization of r is compensated in the s cofactor so the
    // Bezout identity s*u = r (mod m) holds throughout.
    UPoly mm = m;
    mm.makeMonic();
    UPoly r0 = mm;
    UPoly r1 = u % mm;
    UPoly s0, s1(Rational(keel::i64{1}));
    if (!r1.isZero()) {
        s1 = s1 * (Rational(keel::i64{1}) / r1.lc());
        r1.makeMonic();
    }
    while (!r1.isZero()) {
        UPoly q, r;
        UPoly::divMod(r0, r1, q, r);
        UPoly s2 = s0 - q * s1;
        r0 = r1;
        s0 = s1;
        s1 = s2;
        if (!r.isZero()) {
            s1 = s1 * (Rational(keel::i64{1}) / r.lc());
            r.makeMonic();
        }
        r1 = r;
    }
    assert(r0.isConst() && !r0.isZero() && "invMod: gcd is not a constant");
    return s0; // r0 is the monic constant 1, so s0*u == 1 (mod m)
}

UPoly UPoly::derivative() const
{
    UPoly out;
    if (c_.size() <= 1)
        return out;
    out.c_.reserve(c_.size() - 1);
    for (keel::usize i = 1; i < c_.size(); ++i)
        out.c_.push_back(c_[i] * Rational(keel::as<keel::i64>(i)));
    out.trim();
    return out;
}

UPoly UPoly::powUInt(keel::u64 n) const
{
    UPoly result(Rational(keel::i64{1}));
    UPoly base = *this;
    while (n != 0) {
        if (n & 1)
            result = result * base;
        n >>= 1;
        if (n != 0)
            base = base * base;
    }
    return result;
}

UPoly UPoly::gcd(const UPoly &a, const UPoly &b)
{
    // Monic Euclidean loop: normalizing every remainder keeps the
    // rational coefficients at polynomial growth instead of the
    // exponential blow-up of the raw PRS — the residue sweeps call
    // this gcd once per rational residue with big fractional inputs.
    UPoly x = a, y = b;
    if (!y.isZero())
        y.makeMonic();
    while (!y.isZero()) {
        UPoly q, r;
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

UPoly UPoly::squarefreePart() const
{
    if (isZero())
        return UPoly();
    const UPoly g = gcd(*this, derivative());
    if (g.isConst())
        return *this;
    UPoly q, r;
    divMod(*this, g, q, r);
    assert(r.isZero());
    return q;
}

keel::Array<UPoly> UPoly::squarefreeDecomposition() const
{
    assert(!isZero() && "squarefreeDecomposition of zero");
    // Yun's algorithm operates on the monic associate; the identity
    // A == lc(A) * F_1^1 * ... * F_k^k carries the scalar separately.
    UPoly am = *this;
    am.makeMonic();
    const UPoly d = am.derivative();
    const UPoly c = gcd(am, d);

    UPoly q, r;
    divMod(am, c, q, r);
    UPoly w = q;
    divMod(d, c, q, r);
    UPoly v = q;

    keel::Array<UPoly> out;
    const UPoly one(Rational(keel::i64{1}));
    while (!(w == one)) {
        const UPoly z = v - w.derivative();
        const UPoly f = gcd(w, z);
        out.push_back(f);
        divMod(w, f, q, r);
        w = q;
        divMod(z, f, q, r);
        v = q;
    }
    return out;
}

// Resultant via the exact Euclidean recursion over Q:
//   res(A, B) = (-1)^(deg A * deg B) * res(B, A)
//   res(A, c) = c^(deg A)                    (constant c)
//   res(A, B) = lc(B)^(deg A - deg R) * res(R, B),  A = Q*B + R
// Coefficients stay exact (Rational); the subresultant/PRS form over Z
// is a performance upgrade, not a correctness one.
Rational UPoly::resultant(const UPoly &a, const UPoly &b)
{
    if (a.isZero() || b.isZero())
        return Rational(keel::i64{0});

    const UPoly *hi = &a, *lo = &b;
    if (hi->deg() < lo->deg()) {
        std::swap(hi, lo);
        const keel::i64 mn = keel::as<keel::i64>(a.deg()) *
                             keel::as<keel::i64>(b.deg());
        if (mn & 1)
            return -resultant(*hi, *lo);
        return resultant(*hi, *lo);
    }

    if (lo->deg() == 0)
        return Rational::powUInt(lo->lc(), keel::as<keel::u64>(hi->deg()));

    UPoly q, r;
    divMod(*hi, *lo, q, r);
    if (r.isZero())
        return Rational(keel::i64{0});
    const Rational factor = Rational::powUInt(
        lo->lc(), keel::as<keel::u64>(hi->deg() - r.deg()));
    return factor * resultant(r, *lo);
}

bool operator==(const UPoly &a, const UPoly &b)
{
    return a.c_ == b.c_;
}

bool operator!=(const UPoly &a, const UPoly &b)
{
    return !(a == b);
}

keel::String UPoly::toString(const char *var) const
{
    if (isZero())
        return keel::String::from("0");
    keel::String out;
    for (keel::usize k = c_.size(); k-- > 0;) {
        if (c_[k].isZero())
            continue;
        const bool negative = c_[k].signum() < 0;
        const Rational mag = c_[k].abs();
        if (out.empty()) {
            if (negative)
                out.push_back('-');
        } else {
            out.append(negative ? " - " : " + ");
        }
        const bool isOne = mag == Rational(keel::i64{1});
        if (k == 0 || !isOne)
            out.append(mag.toString());
        if (k > 0) {
            if (!isOne)
                out.push_back('*');
            out.append(var);
            if (k > 1) {
                keel::format_into(out, "^{}", k);
            }
        }
    }
    return out;
}

} // namespace numkit::cas
