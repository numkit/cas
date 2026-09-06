#include <numkit/cas/poly/upoly.hpp>

#include <algorithm>
#include <cassert>

namespace numkit::cas {

UPoly::UPoly(Rational c)
{
    if (!c.isZero())
        c_.push_back(std::move(c));
}

UPoly::UPoly(std::vector<Rational> coeffs) : c_(std::move(coeffs))
{
    trim();
}

UPoly UPoly::monomial(Rational c, std::uint64_t exp)
{
    UPoly out;
    if (!c.isZero()) {
        out.c_.assign(static_cast<std::size_t>(exp) + 1,
                      Rational(std::int64_t{0}));
        out.c_[static_cast<std::size_t>(exp)] = std::move(c);
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
    const Rational inv = Rational(std::int64_t{1}) / lc();
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
    Rational acc(std::int64_t{0});
    for (std::size_t i = c_.size(); i-- > 0;)
        acc = acc * x + c_[i];
    return acc;
}

UPoly operator+(const UPoly &a, const UPoly &b)
{
    UPoly out;
    out.c_.reserve(std::max(a.c_.size(), b.c_.size()));
    for (std::size_t i = 0; i < std::max(a.c_.size(), b.c_.size()); ++i)
        out.c_.push_back(a.coeff(i) + b.coeff(i));
    out.trim();
    return out;
}

UPoly operator-(const UPoly &a, const UPoly &b)
{
    UPoly out;
    out.c_.reserve(std::max(a.c_.size(), b.c_.size()));
    for (std::size_t i = 0; i < std::max(a.c_.size(), b.c_.size()); ++i)
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
    out.c_.assign(a.c_.size() + b.c_.size() - 1, Rational(std::int64_t{0}));
    for (std::size_t i = 0; i < a.c_.size(); ++i)
        for (std::size_t j = 0; j < b.c_.size(); ++j)
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
    r = a;
    q = UPoly();
    if (a.isZero() || a.deg() < b.deg())
        return;
    q.c_.assign(static_cast<std::size_t>(a.deg() - b.deg()) + 1,
                Rational(std::int64_t{0}));
    const Rational blcInv = Rational(std::int64_t{1}) / b.lc();
    while (!r.isZero() && r.deg() >= b.deg()) {
        const int shift = r.deg() - b.deg();
        const Rational f = r.lc() * blcInv;
        q.c_[static_cast<std::size_t>(shift)] += f;
        for (std::size_t j = 0; j < b.c_.size(); ++j)
            r.c_[j + static_cast<std::size_t>(shift)] -= f * b.c_[j];
        r.trim();
    }
}

UPoly UPoly::derivative() const
{
    UPoly out;
    if (c_.size() <= 1)
        return out;
    out.c_.reserve(c_.size() - 1);
    for (std::size_t i = 1; i < c_.size(); ++i)
        out.c_.push_back(c_[i] * Rational(static_cast<std::int64_t>(i)));
    out.trim();
    return out;
}

UPoly UPoly::powUInt(std::uint64_t n) const
{
    UPoly result(Rational(std::int64_t{1}));
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
    UPoly x = a, y = b;
    while (!y.isZero()) {
        UPoly q, r;
        divMod(x, y, q, r);
        x = y;
        y = r;
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

std::vector<UPoly> UPoly::squarefreeDecomposition() const
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

    std::vector<UPoly> out;
    const UPoly one(Rational(std::int64_t{1}));
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
        return Rational(std::int64_t{0});

    const UPoly *hi = &a, *lo = &b;
    if (hi->deg() < lo->deg()) {
        std::swap(hi, lo);
        const long long mn = static_cast<long long>(a.deg()) *
                             static_cast<long long>(b.deg());
        if (mn & 1)
            return -resultant(*hi, *lo);
        return resultant(*hi, *lo);
    }

    if (lo->deg() == 0)
        return Rational::powUInt(lo->lc(), static_cast<std::uint64_t>(hi->deg()));

    UPoly q, r;
    divMod(*hi, *lo, q, r);
    if (r.isZero())
        return Rational(std::int64_t{0});
    const Rational factor = Rational::powUInt(
        lo->lc(), static_cast<std::uint64_t>(hi->deg() - r.deg()));
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

std::string UPoly::toString(const char *var) const
{
    if (isZero())
        return "0";
    std::string out;
    for (std::size_t k = c_.size(); k-- > 0;) {
        if (c_[k].isZero())
            continue;
        const bool negative = c_[k].signum() < 0;
        const Rational mag = c_[k].abs();
        if (out.empty())
            out = negative ? "-" : "";
        else
            out += negative ? " - " : " + ";
        const bool isOne = mag == Rational(std::int64_t{1});
        if (k == 0 || !isOne)
            out += mag.toString();
        if (k > 0) {
            if (!isOne)
                out += "*";
            out += var;
            if (k > 1) {
                out += "^";
                out += std::to_string(k);
            }
        }
    }
    return out;
}

} // namespace numkit::cas
