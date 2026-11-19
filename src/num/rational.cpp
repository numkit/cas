#include <keel/core.h>
#include <numkit/cas/num/rational.hpp>

#include <cassert>
#include <cmath>

namespace numkit::cas {

Rational Rational::fromDoubleBits(double v)
{
    assert(std::isfinite(v) && "fromDoubleBits: non-finite double");
    int e = 0;
    const double f = std::frexp(v, &e); // v == f * 2^e, f in [0.5, 1)
    // f has at most 53 significand bits (incl. the hidden one), so
    // f * 2^53 is an exact integer that itself fits a double.
    const keel::i64 m = static_cast<keel::i64>(f * 9007199254740992.0);
    if (m == 0)
        return Rational(); // +-0.0
    const int shift = e - 53;
    if (shift >= 0)
        return Rational(BigInt(m) * BigInt::powUInt(BigInt(2),
                                                    static_cast<keel::u64>(shift)),
                        BigInt(1));
    return Rational(BigInt(m),
                    BigInt::powUInt(BigInt(2),
                                    static_cast<keel::u64>(-shift)));
}

double Rational::toDouble() const
{
    if (num_.isZero())
        return 0.0;
    if (den_ == BigInt(1))
        return num_.toDouble();
    const keel::usize bn = num_.bitLength();
    const keel::usize bd = den_.bitLength();
    if (bn <= 53 && bd <= 53) {
        const double v = static_cast<double>(num_.lowLimb()) /
                         static_cast<double>(den_.lowLimb());
        return num_.isNegative() ? -v : v;
    }
    const BigInt N = num_.abs();
    const BigInt &D = den_;
    int shift = 54 - (static_cast<int>(bn) - static_cast<int>(bd));
    BigInt Ns = shift >= 0 ? (N << static_cast<keel::usize>(shift)) : N;
    BigInt Ds = shift < 0 ? (D << static_cast<keel::usize>(-shift)) : D;
    if (Ns < (Ds << 54)) {
        Ns = Ns << 1;
        ++shift;
    } else if (Ns >= (Ds << 55)) {
        Ds = Ds << 1;
        --shift;
    }
    BigInt Q, R;
    BigInt::divMod(Ns, Ds, Q, R);
    const keel::u64 q64 = Q.lowLimb();
    keel::u64 mant53 = q64 >> 2;
    const bool guard = ((q64 >> 1) & 1ULL) != 0;
    const bool sticky = ((q64 & 1ULL) != 0) || !R.isZero();
    if (guard && (sticky || (mant53 & 1ULL) != 0))
        ++mant53;
    const double scaled = std::ldexp(static_cast<double>(mant53), 2 - shift);
    return num_.isNegative() ? -scaled : scaled;
}

Rational::Rational(keel::i64 v) : num_(v), den_(1) {}

Rational::Rational(keel::u64 v) : num_(v), den_(1) {}

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

Rational Rational::powUInt(const Rational &base, keel::u64 exp)
{
    Rational result(keel::i64{1});
    Rational b = base;
    while (exp != 0) {
        if (exp & 1)
            result = result * b;
        exp >>= 1;
        if (exp != 0)
            b = b * b;
    }
    return result;
}

keel::u64 Rational::hashBits() const
{
    return (num().hashBits() * 0x9E3779B97F4A7C15ULL) ^
           (den().hashBits() + 0x165667B19E3779F9ULL);
}

bool Rational::fitsInt64(keel::i64 &out) const
{
    if (!(den() == BigInt(1)))
        return false;
    return num().fitsInt64(out);
}

keel::String Rational::toString() const
{
    if (den() == BigInt(1))
        return num().toString();
    keel::String out = num().toString();
    out.push_back('/');
    out.append(den().toString());
    return out;
}

bool Rational::tryParse(Rational &out, keel::StringRef s)
{
    out = Rational();
    const keel::usize slash = s.find('/');
    if (slash == keel::kInvalidIndex) {
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
