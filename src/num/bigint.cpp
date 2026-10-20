#include <numkit/cas/num/bigint.hpp>

#include <algorithm>
#include <cassert>
#include <cmath>
#include <limits>

namespace numkit::cas {

namespace {

constexpr std::uint64_t kPow10_19 = 10000000000000000000ULL; // 10^19 < 2^64

const std::uint64_t kPow10[20] = {
    1ULL,
    10ULL,
    100ULL,
    1000ULL,
    10000ULL,
    100000ULL,
    1000000ULL,
    10000000ULL,
    100000000ULL,
    1000000000ULL,
    10000000000ULL,
    100000000000ULL,
    1000000000000ULL,
    10000000000000ULL,
    100000000000000ULL,
    1000000000000000ULL,
    10000000000000000ULL,
    100000000000000000ULL,
    1000000000000000000ULL,
    10000000000000000000ULL,
};

int nlz32(std::uint32_t x)
{
    int n = 0;
    if (x == 0)
        return 32;
    if ((x >> 16) == 0) { n += 16; x <<= 16; }
    if ((x >> 24) == 0) { n += 8;  x <<= 8; }
    if ((x >> 28) == 0) { n += 4;  x <<= 4; }
    if ((x >> 30) == 0) { n += 2;  x <<= 2; }
    if ((x >> 31) == 0) { n += 1; }
    return n;
}

int nlz64(std::uint64_t x)
{
    if (x == 0)
        return 64;
    std::uint32_t hi = static_cast<std::uint32_t>(x >> 32);
    return hi != 0 ? nlz32(hi) : 32 + nlz32(static_cast<std::uint32_t>(x));
}

// Full 64x64 -> 128-bit product without intrinsics or __int128 (MSVC-portable).
void mulu64(std::uint64_t a, std::uint64_t b, std::uint64_t *lo, std::uint64_t *hi)
{
    const std::uint64_t mask = 0xFFFFFFFFULL;
    const std::uint64_t aL = a & mask, aH = a >> 32;
    const std::uint64_t bL = b & mask, bH = b >> 32;
    const std::uint64_t ll = aL * bL;
    const std::uint64_t lh = aL * bH;
    const std::uint64_t hl = aH * bL;
    const std::uint64_t hh = aH * bH;
    const std::uint64_t mid = lh + hl;
    const std::uint64_t midCarry = (mid < lh) ? 1ULL : 0ULL;
    const std::uint64_t loRes = ll + (mid << 32);
    const std::uint64_t loCarry = (loRes < ll) ? 1ULL : 0ULL;
    *lo = loRes;
    *hi = hh + (mid >> 32) + (midCarry << 32) + loCarry;
}

template <typename LimbContainer>
void toDigits32(const LimbContainer &limbs, std::vector<std::uint32_t> &d)
{
    d.clear();
    d.reserve(limbs.size() * 2);
    for (std::uint64_t l : limbs) {
        d.push_back(static_cast<std::uint32_t>(l));
        d.push_back(static_cast<std::uint32_t>(l >> 32));
    }
    while (!d.empty() && d.back() == 0)
        d.pop_back();
}

template <typename LimbContainer>
void fromDigits32(const std::vector<std::uint32_t> &d, LimbContainer &limbs)
{
    limbs.assign((d.size() + 1) / 2, 0);
    for (std::size_t i = 0; i < d.size(); ++i) {
        if (i & 1)
            limbs[i >> 1] |= static_cast<std::uint64_t>(d[i]) << 32;
        else
            limbs[i >> 1] |= d[i];
    }
    while (!limbs.empty() && limbs.back() == 0)
        limbs.pop_back();
}

// Knuth algorithm D (Hacker's Delight divmnu) on base-2^32 digits.
// Digits are little-endian with no leading zero digit; u may be empty.
void divModDigits(const std::vector<std::uint32_t> &u,
                  const std::vector<std::uint32_t> &v,
                  std::vector<std::uint32_t> &q,
                  std::vector<std::uint32_t> &r)
{
    const std::size_t m = u.size();
    const std::size_t n = v.size();

    if (n > m) {
        q.clear();
        r = u;
        return;
    }

    if (n == 1) {
        q.assign(m, 0);
        std::uint64_t k = 0;
        for (std::size_t j = m; j-- > 0;) {
            const std::uint64_t t = (k << 32) | u[j];
            q[j] = static_cast<std::uint32_t>(t / v[0]);
            k = t % v[0];
        }
        r.assign(1, static_cast<std::uint32_t>(k));
        while (q.size() > 1 && q.back() == 0)
            q.pop_back();
        return;
    }

    const int s = nlz32(v[n - 1]);
    std::vector<std::uint32_t> vn(n), un(m + 1, 0);

    for (std::size_t i = n; i-- > 1;)
        vn[i] = s ? (v[i] << s) | (v[i - 1] >> (32 - s)) : v[i];
    vn[0] = v[0] << s;

    for (std::size_t i = m; i-- > 1;)
        un[i] = s ? (u[i] << s) | (u[i - 1] >> (32 - s)) : u[i];
    un[0] = u[0] << s;
    un[m] = s ? u[m - 1] >> (32 - s) : 0;

    q.assign(m - n + 1, 0);

    for (std::size_t j = m - n + 1; j-- > 0;) {
        const std::uint64_t num =
            (static_cast<std::uint64_t>(un[j + n]) << 32) | un[j + n - 1];
        std::uint64_t qhat = num / vn[n - 1];
        std::uint64_t rhat = num % vn[n - 1];

        while (qhat >= (1ULL << 32) ||
               qhat * vn[n - 2] > ((rhat << 32) | un[j + n - 2])) {
            qhat--;
            rhat += vn[n - 1];
            if (rhat >= (1ULL << 32))
                break;
        }

        std::uint64_t k = 0;
        for (std::size_t i = 0; i < n; ++i) {
            const std::uint64_t p = qhat * vn[i];
            const std::uint64_t sub = k + (p & 0xFFFFFFFFULL);
            const std::uint64_t cur = un[i + j];
            un[i + j] = static_cast<std::uint32_t>(cur - sub);
            const std::uint64_t deficit = sub > cur ? sub - cur : 0;
            k = (p >> 32) + ((deficit + 0xFFFFFFFFULL) >> 32);
        }
        const bool negative = k > un[j + n];
        un[j + n] = static_cast<std::uint32_t>(un[j + n] - k);

        q[j] = static_cast<std::uint32_t>(qhat);

        if (negative) {
            q[j] -= 1;
            std::uint64_t carry = 0;
            for (std::size_t i = 0; i < n; ++i) {
                const std::uint64_t t =
                    static_cast<std::uint64_t>(un[i + j]) + vn[i] + carry;
                un[i + j] = static_cast<std::uint32_t>(t);
                carry = t >> 32;
            }
            un[j + n] = static_cast<std::uint32_t>(un[j + n] + carry);
        }
    }

    while (q.size() > 1 && q.back() == 0)
        q.pop_back();

    r.assign(n, 0);
    for (std::size_t i = 0; i + 1 < n; ++i)
        r[i] = s ? (un[i] >> s) | (un[i + 1] << (32 - s)) : un[i];
    r[n - 1] = un[n - 1] >> s;
    while (r.size() > 1 && r.back() == 0)
        r.pop_back();
}

} // namespace

BigInt::BigInt(std::int64_t v) noexcept
{
    if (v == 0)
        return;
    negative_ = v < 0;
    limbs_.push_back(negative_ ? ~static_cast<std::uint64_t>(v) + 1
                               : static_cast<std::uint64_t>(v));
}

BigInt::BigInt(std::uint64_t v) noexcept
{
    if (v != 0)
        limbs_.push_back(v);
}

void BigInt::normalize() noexcept
{
    while (!limbs_.empty() && limbs_.back() == 0)
        limbs_.pop_back();
    if (limbs_.empty())
        negative_ = false;
}

int BigInt::signum() const noexcept
{
    if (limbs_.empty())
        return 0;
    return negative_ ? -1 : 1;
}

std::size_t BigInt::bitLength() const noexcept
{
    if (limbs_.empty())
        return 0;
    return (limbs_.size() - 1) * 64 + (64 - nlz64(limbs_.back()));
}

int BigInt::compareMagnitude(const BigInt &o) const noexcept
{
    if (limbs_.size() != o.limbs_.size())
        return limbs_.size() < o.limbs_.size() ? -1 : 1;
    for (std::size_t i = limbs_.size(); i-- > 0;) {
        if (limbs_[i] != o.limbs_[i])
            return limbs_[i] < o.limbs_[i] ? -1 : 1;
    }
    return 0;
}

BigInt BigInt::addMagnitude(const BigInt &a, const BigInt &b)
{
    const LimbVec &big =
        a.limbs_.size() >= b.limbs_.size() ? a.limbs_ : b.limbs_;
    const LimbVec &small =
        a.limbs_.size() >= b.limbs_.size() ? b.limbs_ : a.limbs_;

    BigInt out;
    out.limbs_.reserve(big.size() + 1);
    std::uint64_t carry = 0;
    for (std::size_t i = 0; i < small.size(); ++i) {
        const std::uint64_t t = big[i] + small[i];
        const std::uint64_t c1 = (t < big[i]) ? 1 : 0;
        const std::uint64_t t2 = t + carry;
        const std::uint64_t c2 = (t2 < t) ? 1 : 0;
        out.limbs_.push_back(t2);
        carry = c1 + c2;
    }
    for (std::size_t i = small.size(); i < big.size(); ++i) {
        const std::uint64_t t = big[i] + carry;
        carry = (t < carry) ? 1 : 0;
        out.limbs_.push_back(t);
    }
    if (carry)
        out.limbs_.push_back(1);
    return out;
}

BigInt BigInt::subMagnitude(const BigInt &a, const BigInt &b)
{
    BigInt out;
    out.limbs_.reserve(a.limbs_.size());
    std::uint64_t borrow = 0;
    for (std::size_t i = 0; i < b.limbs_.size(); ++i) {
        const std::uint64_t t = a.limbs_[i] - b.limbs_[i];
        const std::uint64_t b1 = (a.limbs_[i] < b.limbs_[i]) ? 1 : 0;
        const std::uint64_t t2 = t - borrow;
        const std::uint64_t b2 = (t < borrow) ? 1 : 0;
        out.limbs_.push_back(t2);
        borrow = b1 + b2;
    }
    for (std::size_t i = b.limbs_.size(); i < a.limbs_.size(); ++i) {
        const std::uint64_t t = a.limbs_[i] - borrow;
        borrow = (t > a.limbs_[i]) ? 1 : 0;
        out.limbs_.push_back(t);
    }
    out.normalize();
    return out;
}

BigInt operator+(const BigInt &a, const BigInt &b)
{
    BigInt out;
    if (a.negative_ == b.negative_) {
        out = BigInt::addMagnitude(a, b);
        out.negative_ = a.negative_;
        out.normalize();
        return out;
    }
    const int cmp = a.compareMagnitude(b);
    if (cmp == 0)
        return BigInt();
    if (cmp > 0) {
        out = BigInt::subMagnitude(a, b);
        out.negative_ = a.negative_;
    } else {
        out = BigInt::subMagnitude(b, a);
        out.negative_ = b.negative_;
    }
    out.normalize();
    return out;
}

BigInt operator-(const BigInt &a, const BigInt &b)
{
    BigInt negB = b;
    negB.negative_ = !b.negative_;
    negB.normalize();
    return a + negB;
}

BigInt operator*(const BigInt &a, const BigInt &b)
{
    if (a.isZero() || b.isZero())
        return BigInt();
    BigInt out;
    out.limbs_.assign(a.limbs_.size() + b.limbs_.size(), 0);
    for (std::size_t i = 0; i < a.limbs_.size(); ++i) {
        std::uint64_t carry = 0;
        for (std::size_t j = 0; j < b.limbs_.size(); ++j) {
            std::uint64_t lo, hi;
            mulu64(a.limbs_[i], b.limbs_[j], &lo, &hi);
            const std::uint64_t t = out.limbs_[i + j] + lo;
            const std::uint64_t c1 = (t < lo) ? 1 : 0;
            const std::uint64_t t2 = t + carry;
            const std::uint64_t c2 = (t2 < t) ? 1 : 0;
            out.limbs_[i + j] = t2;
            carry = hi + c1 + c2;
        }
        std::size_t k = i + b.limbs_.size();
        while (carry != 0) {
            const std::uint64_t t = out.limbs_[k] + carry;
            carry = (t < carry) ? 1 : 0;
            out.limbs_[k] = t;
            ++k;
        }
    }
    out.negative_ = a.negative_ != b.negative_;
    out.normalize();
    return out;
}

void BigInt::divMod(const BigInt &a, const BigInt &b, BigInt &q, BigInt &r)
{
    assert(!b.isZero() && "BigInt::divMod division by zero");
    q = BigInt();
    r = BigInt();
    if (a.isZero())
        return;

    if (a.limbs_.size() == 1 && b.limbs_.size() == 1) {
        const std::uint64_t ua = a.limbs_[0];
        const std::uint64_t ub = b.limbs_[0];
        const std::uint64_t uq = ua / ub;
        const std::uint64_t ur = ua % ub;
        if (uq != 0) {
            q.limbs_.push_back(uq);
            q.negative_ = (a.negative_ != b.negative_);
        }
        if (ur != 0) {
            r.limbs_.push_back(ur);
            r.negative_ = a.negative_;
        }
        return;
    }

    std::vector<std::uint32_t> ud, vd, qd, rd;
    toDigits32(a.limbs_, ud);
    toDigits32(b.limbs_, vd);
    divModDigits(ud, vd, qd, rd);

    fromDigits32(qd, q.limbs_);
    fromDigits32(rd, r.limbs_);
    q.negative_ = (a.negative_ != b.negative_) && !q.limbs_.empty();
    r.negative_ = a.negative_ && !r.limbs_.empty();
}

BigInt operator/(const BigInt &a, const BigInt &b)
{
    BigInt q, r;
    BigInt::divMod(a, b, q, r);
    return q;
}

BigInt operator%(const BigInt &a, const BigInt &b)
{
    BigInt q, r;
    BigInt::divMod(a, b, q, r);
    return r;
}

bool operator==(const BigInt &a, const BigInt &b)
{
    return a.negative_ == b.negative_ && a.limbs_ == b.limbs_;
}

bool operator!=(const BigInt &a, const BigInt &b)
{
    return !(a == b);
}

bool operator<(const BigInt &a, const BigInt &b)
{
    if (a.negative_ != b.negative_)
        return a.negative_;
    const int cmp = a.compareMagnitude(b);
    return a.negative_ ? cmp > 0 : cmp < 0;
}

bool operator<=(const BigInt &a, const BigInt &b)
{
    return !(b < a);
}

bool operator>(const BigInt &a, const BigInt &b)
{
    return b < a;
}

bool operator>=(const BigInt &a, const BigInt &b)
{
    return !(a < b);
}

BigInt BigInt::abs() const
{
    BigInt out = *this;
    out.negative_ = false;
    return out;
}

BigInt BigInt::operator-() const
{
    BigInt out = *this;
    if (!out.limbs_.empty())
        out.negative_ = !out.negative_;
    return out;
}

BigInt BigInt::operator<<(std::size_t bits) const
{
    if (isZero())
        return BigInt();
    const std::size_t limbOff = bits / 64;
    const unsigned bitOff = static_cast<unsigned>(bits % 64);
    BigInt out;
    out.negative_ = negative_;
    out.limbs_.assign(limbs_.size() + limbOff + (bitOff ? 1 : 0), 0);
    if (bitOff == 0) {
        for (std::size_t i = 0; i < limbs_.size(); ++i)
            out.limbs_[i + limbOff] = limbs_[i];
    } else {
        std::uint64_t carry = 0;
        for (std::size_t i = 0; i < limbs_.size(); ++i) {
            out.limbs_[i + limbOff] =
                (limbs_[i] << bitOff) | carry;
            carry = limbs_[i] >> (64 - bitOff);
        }
        out.limbs_[limbs_.size() + limbOff] = carry;
    }
    out.normalize();
    return out;
}

BigInt BigInt::operator>>(std::size_t bits) const
{
    if (isZero())
        return BigInt();
    const std::size_t limbOff = bits / 64;
    const unsigned bitOff = static_cast<unsigned>(bits % 64);

    bool dropped = false;
    for (std::size_t i = 0; i < limbOff && i < limbs_.size(); ++i)
        if (limbs_[i] != 0)
            dropped = true;
    if (bitOff != 0 && limbOff < limbs_.size())
        if ((limbs_[limbOff] & ((1ULL << bitOff) - 1)) != 0)
            dropped = true;

    BigInt out;
    if (limbOff >= limbs_.size()) {
        if (negative_ && dropped)
            return BigInt(-1);
        return BigInt();
    }
    out.limbs_.assign(limbs_.size() - limbOff, 0);
    if (bitOff == 0) {
        for (std::size_t i = 0; i < out.limbs_.size(); ++i)
            out.limbs_[i] = limbs_[i + limbOff];
    } else {
        for (std::size_t i = 0; i < out.limbs_.size(); ++i) {
            const std::uint64_t hi =
                (i + limbOff + 1 < limbs_.size())
                    ? limbs_[i + limbOff + 1] << (64 - bitOff)
                    : 0;
            out.limbs_[i] = (limbs_[i + limbOff] >> bitOff) | hi;
        }
    }
    out.negative_ = negative_;
    out.normalize();
    if (negative_ && dropped) {
        out = out - BigInt(1);
    }
    return out;
}

BigInt BigInt::gcd(const BigInt &a, const BigInt &b)
{
    if (a.limbs_.size() <= 1 && b.limbs_.size() <= 1) {
        std::uint64_t u = a.lowLimb();
        std::uint64_t v = b.lowLimb();
        while (v != 0) {
            const std::uint64_t t = u % v;
            u = v;
            v = t;
        }
        return BigInt(u);
    }
    BigInt x = a.abs();
    BigInt y = b.abs();
    while (!y.isZero()) {
        if (x.limbs_.size() <= 1 && y.limbs_.size() <= 1) {
            std::uint64_t u = x.lowLimb();
            std::uint64_t v = y.lowLimb();
            while (v != 0) {
                const std::uint64_t t = u % v;
                u = v;
                v = t;
            }
            return BigInt(u);
        }
        BigInt q, r;
        divMod(x, y, q, r);
        x = std::move(y);
        y = std::move(r);
    }
    return x;
}

BigInt BigInt::powUInt(const BigInt &base, std::uint64_t exp)
{
    BigInt result(1);
    BigInt b = base;
    while (exp != 0) {
        if (exp & 1)
            result = result * b;
        exp >>= 1;
        if (exp != 0)
            b = b * b;
    }
    return result;
}

BigInt BigInt::lcm(const BigInt &a, const BigInt &b)
{
    if (a.isZero() || b.isZero())
        return BigInt();
    return (a * b).abs() / gcd(a, b);
}

bool BigInt::sqrtExact(BigInt &out) const
{
    if (negative_)
        return false;
    if (isZero()) {
        out = BigInt();
        return true;
    }
    // Newton iteration on x -> (x + n/x)/2, started above sqrt(n).
    BigInt x = BigInt(1) << (bitLength() / 2 + 1);
    while (true) {
        BigInt q, r;
        divMod(*this, x, q, r);
        BigInt y = (x + q) >> 1;
        if (y >= x)
            break;
        x = y;
    }
    if (x * x == *this) {
        out = x;
        return true;
    }
    return false;
}

std::uint64_t BigInt::hashBits() const
{
    std::uint64_t h = 0x9E3779B97F4A7C15ULL;
    if (negative_)
        h ^= 0x123456789ABCDEFULL;
    for (std::uint64_t l : limbs_)
        h = (h ^ l) * 0x100000001B3ULL;
    return h;
}

bool BigInt::fitsInt64(std::int64_t &out) const noexcept
{
    if (limbs_.empty()) {
        out = 0;
        return true;
    }
    if (limbs_.size() > 1)
        return false;
    const std::uint64_t m = limbs_[0];
    if (negative_) {
        if (m > (1ULL << 63))
            return false;
        out = (m == (1ULL << 63)) ? std::numeric_limits<std::int64_t>::min()
                                  : -static_cast<std::int64_t>(m);
        return true;
    }
    if (m > static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max()))
        return false;
    out = static_cast<std::int64_t>(m);
    return true;
}

bool BigInt::fitsUint64(std::uint64_t &out) const noexcept
{
    if (limbs_.empty()) {
        out = 0;
        return true;
    }
    if (negative_ || limbs_.size() > 1)
        return false;
    out = limbs_[0];
    return true;
}

double BigInt::toDouble() const noexcept
{
    if (limbs_.empty())
        return 0.0;
    const std::size_t n = limbs_.size();
    if (n == 1) {
        const double v = static_cast<double>(limbs_[0]);
        return negative_ ? -v : v;
    }
    const std::size_t bits = bitLength();
    if (bits > 1024)
        return negative_ ? -std::numeric_limits<double>::infinity()
                         : std::numeric_limits<double>::infinity();
    const std::uint64_t hi = limbs_[n - 1];
    const std::uint64_t lo = limbs_[n - 2];
    const int lz = nlz64(hi);
    // Align the top 64 bits of the magnitude into `top64`.
    const std::uint64_t top64 =
        lz == 0 ? hi : ((hi << lz) | (lo >> (64 - lz)));
    // Round the top 64-bit word to 53 IEEE-754 mantissa bits (round-to-nearest-even).
    std::uint64_t mant53 = top64 >> 11;
    const std::uint64_t rem11 = top64 & 0x7FFULL;
    bool sticky = (rem11 & 0x3FFULL) != 0;
    if (!sticky && lz > 0 && (lo & ((1ULL << (64 - lz)) - 1)) != 0)
        sticky = true;
    for (std::size_t i = 0; !sticky && i + 2 < n; ++i)
        if (limbs_[i] != 0)
            sticky = true;
    if ((rem11 & 0x400ULL) != 0 && (sticky || (mant53 & 1ULL) != 0))
        ++mant53;
    const double scaled =
        std::ldexp(static_cast<double>(mant53), static_cast<int>(bits) - 53);
    return negative_ ? -scaled : scaled;
}

std::string BigInt::toString() const
{
    if (isZero())
        return "0";
    const BigInt chunk(kPow10_19);
    std::string digits;
    BigInt m = abs();
    while (!m.isZero()) {
        BigInt q, r;
        divMod(m, chunk, q, r);
        const std::uint64_t c = r.lowLimb();
        std::string part = std::to_string(c);
        if (!q.isZero())
            part.insert(0, 19 - part.size(), '0');
        digits.insert(0, part);
        m = q;
    }
    if (negative_)
        digits.insert(0, "-");
    return digits;
}

bool BigInt::tryParse(BigInt &out, const std::string &s)
{
    out = BigInt();
    std::size_t i = 0;
    bool negative = false;
    if (i < s.size() && (s[i] == '+' || s[i] == '-')) {
        negative = s[i] == '-';
        ++i;
    }
    if (i >= s.size())
        return false;
    for (char ch : s.substr(i)) {
        if (ch < '0' || ch > '9')
            return false;
    }
    const std::size_t ndigits = s.size() - i;
    std::size_t lead = ndigits % 19;
    if (lead == 0)
        lead = 19;

    BigInt v;
    std::size_t pos = i;
    while (pos < s.size()) {
        std::size_t len = (pos == i) ? lead : 19;
        std::uint64_t c = 0;
        for (std::size_t k = 0; k < len; ++k)
            c = c * 10 + static_cast<std::uint64_t>(s[pos + k] - '0');
        v = v * BigInt(kPow10[len]) + BigInt(c);
        pos += len;
    }
    v.negative_ = negative;
    v.normalize();
    out = v;
    return true;
}

// ============================================================
// Integer factorization: Miller-Rabin + Pollard-Brent rho.
// ============================================================

namespace {

// Fixed xorshift stream for the above-2^64 probabilistic extension
// of isPrime (determinism: same input, same bases, every run).
std::uint64_t factorRngNext(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

BigInt powModBig(const BigInt &base, const BigInt &e, const BigInt &m)
{
    BigInt r = BigInt(1) % m;
    BigInt b = base % m;
    const int bits = static_cast<int>(e.bitLength());
    for (int i = bits - 1; i >= 0; --i) {
        r = r * r % m;
        if ((e >> static_cast<std::size_t>(i)).lowLimb() & 1)
            r = r * b % m;
    }
    return r;
}

// Strong probable prime test of n (odd, > 2, a < n) to base a.
bool strongProbablyPrime(const BigInt &n, const BigInt &a)
{
    const BigInt one(1);
    const BigInt nMinus1 = n - one;
    BigInt d = nMinus1;
    int s = 0;
    while ((d.lowLimb() & 1) == 0) {
        d = d >> 1;
        ++s;
    }
    BigInt x = powModBig(a, d, n);
    if (x == one || x == nMinus1)
        return true;
    for (int r = 1; r < s; ++r) {
        x = x * x % n;
        if (x == nMinus1)
            return true;
    }
    return false;
}

// Pollard rho with Floyd cycles and batched gcd: one gcd per kBatch
// steps over the running product of differences. When the batch
// product jumps straight to n (all prime factors at once) or the walk
// collides, the batch is replayed step by step from its checkpoint —
// a NONZERO step difference can never have gcd == n, so the replay
// returns a proper divisor. Returns n only for a true collision
// without any factor; the caller retries with the next c (a fresh c
// changes the whole trajectory, unlike restarting at x = y = 2).
BigInt pollardRho(const BigInt &n, const BigInt &c)
{
    constexpr std::uint64_t kBatch = 96;
    const BigInt one(1);
    BigInt x(2), y(2);
    for (;;) {
        const BigInt x0 = x, y0 = y;
        BigInt q(1);
        bool collided = false;
        for (std::uint64_t i = 0; i < kBatch; ++i) {
            x = (x * x + c) % n;
            y = (y * y + c) % n;
            y = (y * y + c) % n;
            const BigInt diff = ((x - y) % n).abs();
            if (diff.isZero()) {
                collided = true;
                break;
            }
            q = q * diff % n;
        }
        if (!collided) {
            const BigInt g = BigInt::gcd(q, n);
            if (g == one)
                continue; // clean batch, keep walking
            if (!(g == n))
                return g; // proper divisor from the batch product
            // g == n: the product skipped over the divisor — replay.
        }
        x = x0;
        y = y0;
        for (std::uint64_t i = 0; i < kBatch; ++i) {
            x = (x * x + c) % n;
            y = (y * y + c) % n;
            y = (y * y + c) % n;
            const BigInt diff = ((x - y) % n).abs();
            if (diff.isZero())
                return n; // true collision, no factor for this c
            const BigInt g = BigInt::gcd(diff, n);
            if (!(g == one))
                return g;
        }
    }
}

} // namespace

bool BigInt::isPrime(const BigInt &n)
{
    static const std::uint64_t kBases[] = {2,  3,  5,  7,  11, 13, 17,
                                           19, 23, 29, 31, 37};
    if (n < BigInt(2))
        return false;
    for (std::uint64_t b : kBases) {
        const BigInt bb(b);
        if (n == bb)
            return true;
        BigInt q, r;
        divMod(n, bb, q, r);
        if (r.isZero())
            return false;
    }
    // n is odd, > 37 and coprime to all bases; here n > every base.
    std::uint64_t fits;
    const bool below2e64 = n.fitsUint64(fits);
    for (std::uint64_t b : kBases)
        if (!strongProbablyPrime(n, BigInt(b)))
            return false;
    if (below2e64)
        return true; // the 12 bases are complete below 2^64
    // Probabilistic extension: 38 more fixed-stream bases.
    std::uint64_t rng = 0x9E3779B97F4A7C15ULL;
    const BigInt span = n - BigInt(2);
    for (int i = 0; i < 38; ++i) {
        const BigInt a = BigInt(factorRngNext(rng)) % span + BigInt(2);
        if (!strongProbablyPrime(n, a))
            return false;
    }
    return true;
}

std::vector<std::pair<BigInt, int>> BigInt::factorize(const BigInt &nIn)
{
    assert(!(nIn < BigInt(1)) && "factorize expects n >= 1");
    std::vector<std::pair<BigInt, int>> out;
    if (nIn == BigInt(1))
        return out;
    BigInt n = nIn;
    static const std::uint64_t kSmall[] = {2, 3, 5, 7, 11, 13,
                                           17, 19, 23, 29, 31, 37};
    for (std::uint64_t p : kSmall) {
        int e = 0;
        for (;;) {
            BigInt q, r;
            divMod(n, BigInt(p), q, r);
            if (!r.isZero())
                break;
            n = q;
            ++e;
        }
        if (e != 0)
            out.emplace_back(BigInt(p), e);
    }
    std::vector<BigInt> rest;
    if (!(n == BigInt(1)))
        rest.push_back(n);
    while (!rest.empty()) {
        const BigInt m = rest.back();
        rest.pop_back();
        if (m == BigInt(1))
            continue;
        if (isPrime(m)) {
            bool merged = false;
            for (auto &pe : out) {
                if (pe.first == m) {
                    ++pe.second;
                    merged = true;
                    break;
                }
            }
            if (!merged)
                out.emplace_back(m, 1);
            continue;
        }
        BigInt d(1);
        for (std::uint64_t c = 1;; ++c) {
            d = pollardRho(m, BigInt(c));
            if (!(d == BigInt(1)) && !(d == m))
                break;
        }
        rest.push_back(d);
        rest.push_back(m / d);
    }
    std::sort(out.begin(), out.end(),
              [](const std::pair<BigInt, int> &a,
                 const std::pair<BigInt, int> &b) {
                  return a.first < b.first;
              });
    return out;
}

} // namespace numkit::cas
