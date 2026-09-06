#include <numkit/cas/num/rational.hpp>

#include <cassert>

namespace numkit::cas {

Rational::Rational(std::int64_t v) : num_(v), den_(1) {}

Rational::Rational(std::uint64_t v) : num_(v), den_(1) {}

Rational::Rational(BigInt p, BigInt q) : num_(std::move(p)), den_(std::move(q))
{
    canonicalize();
}

void Rational::canonicalize()
{
    assert(!den_.isZero() && "Rational denominator must be non-zero");
    if (num_.isZero()) {
        den_ = BigInt(1);
        return;
    }
    if (den_.isNegative()) {
        num_ = -num_;
        den_ = -den_;
    }
    const BigInt g = BigInt::gcd(num_, den_);
    if (g > BigInt(1)) {
        num_ = num_ / g;
        den_ = den_ / g;
    }
}

Rational Rational::operator-() const
{
    Rational out;
    out.num_ = -num_;
    out.den_ = den_;
    return out;
}

Rational Rational::abs() const
{
    Rational out = *this;
    out.num_ = num_.abs();
    return out;
}

Rational operator+(const Rational &a, const Rational &b)
{
    return Rational(a.num() * b.den() + b.num() * a.den(),
                    a.den() * b.den());
}

Rational operator-(const Rational &a, const Rational &b)
{
    return Rational(a.num() * b.den() - b.num() * a.den(),
                    a.den() * b.den());
}

Rational operator*(const Rational &a, const Rational &b)
{
    return Rational(a.num() * b.num(), a.den() * b.den());
}

Rational operator/(const Rational &a, const Rational &b)
{
    assert(!b.isZero() && "Rational division by zero");
    return Rational(a.num() * b.den(), a.den() * b.num());
}

bool operator==(const Rational &a, const Rational &b)
{
    return a.num() == b.num() && a.den() == b.den();
}

bool operator!=(const Rational &a, const Rational &b)
{
    return !(a == b);
}

bool operator<(const Rational &a, const Rational &b)
{
    return a.num() * b.den() < b.num() * a.den();
}

bool operator<=(const Rational &a, const Rational &b)
{
    return !(b < a);
}

bool operator>(const Rational &a, const Rational &b)
{
    return b < a;
}

bool operator>=(const Rational &a, const Rational &b)
{
    return !(a < b);
}

bool Rational::fitsInt64(std::int64_t &out) const
{
    if (!(den() == BigInt(1)))
        return false;
    return num().fitsInt64(out);
}

std::string Rational::toString() const
{
    if (den() == BigInt(1))
        return num().toString();
    return num().toString() + "/" + den().toString();
}

bool Rational::tryParse(Rational &out, const std::string &s)
{
    out = Rational();
    const std::size_t slash = s.find('/');
    if (slash == std::string::npos) {
        BigInt v;
        if (!BigInt::tryParse(v, s))
            return false;
        out = Rational(std::move(v), BigInt(1));
        return true;
    }
    BigInt p, q;
    if (!BigInt::tryParse(p, s.substr(0, slash)))
        return false;
    if (!BigInt::tryParse(q, s.substr(slash + 1)))
        return false;
    if (q.isZero() || q.isNegative())
        return false;
    out = Rational(std::move(p), std::move(q));
    return true;
}

} // namespace numkit::cas
