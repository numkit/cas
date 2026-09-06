#include <numkit/cas/num/rational.hpp>

#include <limits>
#include <numeric>

#include <gtest/gtest.h>
#include "test_util.hpp"

namespace {

using cas_test::nextU64;
using cas_test::parse;
using cas_test::parseR;
using cas_test::randomBig;
using cas_test::randomRational;
using numkit::cas::BigInt;
using numkit::cas::Rational;

// Python-generated oracle vectors (fractions.Fraction): a, b, a+b, a-b, a*b, a/b.
struct BinCase
{
    const char *a;
    const char *b;
    const char *sum;
    const char *diff;
    const char *prod;
    const char *quot;
};

const BinCase kCases[] = {
    {"1", "1000000000000000000", "1000000000000000001", "-999999999999999999", "1000000000000000000", "1/1000000000000000000"},
    {"9223372036854775807", "1", "9223372036854775808", "9223372036854775806", "9223372036854775807", "9223372036854775807"},
    {"36893488147419103232", "1/2", "73786976294838206465/2", "73786976294838206463/2", "18446744073709551616", "73786976294838206464"},
    {"-1/2", "-1/2", "-1", "0", "1/4", "1"},
    {"2/3", "2", "8/3", "-4/3", "4/3", "1/3"},
    {"1/2", "2", "5/2", "-3/2", "1", "1/4"},
    {"-1", "-1/2", "-3/2", "-1/2", "1/2", "2"},
    {"-56713727820156410577229101238628035243/4052555153018976267", "1", "-56713727820156410573176546085609058976/4052555153018976267", "-56713727820156410581281656391647011510/4052555153018976267", "-56713727820156410577229101238628035243/4052555153018976267", "-56713727820156410577229101238628035243/4052555153018976267"},
    {"0", "999999999999999989/123456789", "999999999999999989/123456789", "-999999999999999989/123456789", "0", "0"},
    {"-1000000000000000000", "1000000000000000000", "0", "-2000000000000000000", "-1000000000000000000000000000000000000", "-1"},
    {"-2", "36893488147419103232", "36893488147419103230", "-36893488147419103234", "-73786976294838206464", "-1/18446744073709551616"},
    {"2", "2", "4", "0", "4", "1"},
    {"320458677408378195770848539959458827076145926046104917932703/156781718793778468590593403654366265590565325", "-1/2", "640917354816756234759978286140449063558888197725944245300081/313563437587556937181186807308732531181130650", "640917354816756548323415873697386244745695506458475426430731/313563437587556937181186807308732531181130650", "-320458677408378195770848539959458827076145926046104917932703/313563437587556937181186807308732531181130650", "-640917354816756391541697079918917654152291852092209835865406/156781718793778468590593403654366265590565325"},
    {"10/7", "-1", "3/7", "17/7", "-10/7", "-10/7"},
    {"18446744073709551615", "-1000000000000000000", "17446744073709551615", "19446744073709551615", "-18446744073709551615000000000000000000", "-3689348814741910323/200000000000000000"},
    {"-9223372036854775808", "1/2", "-18446744073709551615/2", "-18446744073709551617/2", "-4611686018427387904", "-18446744073709551616"},
    {"2", "-56713727820156410577229101238628035243/4052555153018976267", "-56713727820156410569123990932590082709/4052555153018976267", "56713727820156410585334211544665987777/4052555153018976267", "-113427455640312821154458202477256070486/4052555153018976267", "-8105110306037952534/56713727820156410577229101238628035243"},
    {"999999999999999989/123456789", "-1000000000000000000", "-123456788000000000000000011/123456789", "123456789999999999999999989/123456789", "-999999999999999989000000000000000000/123456789", "-999999999999999989/123456789000000000000000000"},
    {"1000000000000000000", "9223372036854775807", "10223372036854775807", "-8223372036854775807", "9223372036854775807000000000000000000", "1000000000000000000/9223372036854775807"},
    {"1", "2", "3", "-1", "2", "1/2"},
    {"9223372036854775807", "18446744073709551615", "27670116110564327422", "-9223372036854775808", "170141183460469231704017187605319778305", "9223372036854775807/18446744073709551615"},
    {"2/3", "-7/5", "-11/15", "31/15", "-14/15", "-10/21"},
    {"1/2", "10/7", "27/14", "-13/14", "5/7", "7/20"},
    {"-1", "2", "1", "-3", "-2", "-1/2"},
    {"-56713727820156410577229101238628035243/4052555153018976267", "1/2", "-113427455640312821150405647324237094219/8105110306037952534", "-113427455640312821158510757630275046753/8105110306037952534", "-56713727820156410577229101238628035243/8105110306037952534", "-113427455640312821154458202477256070486/4052555153018976267"},
    {"0", "-56713727820156410577229101238628035243/4052555153018976267", "-56713727820156410577229101238628035243/4052555153018976267", "56713727820156410577229101238628035243/4052555153018976267", "0", "0"},
};

void expectCanonical(const Rational &v)
{
    EXPECT_FALSE(v.den().isNegative());
    EXPECT_EQ(BigInt::gcd(v.num().abs(), v.den()), BigInt(1));
    if (v.isZero())
        EXPECT_EQ(v.den(), BigInt(1));
}

} // namespace

TEST(RationalConstruction, Canonicalizes)
{
    EXPECT_EQ(Rational(), Rational(0));
    EXPECT_EQ(Rational(BigInt(2), BigInt(4)), parseR("1/2"));
    EXPECT_EQ(Rational(BigInt(-2), BigInt(-4)), parseR("1/2"));
    EXPECT_EQ(Rational(BigInt(-2), BigInt(4)), parseR("-1/2"));
    EXPECT_EQ(Rational(BigInt(0), BigInt(-5)), Rational(0));
    EXPECT_EQ(Rational(BigInt(0), BigInt(7)).den(), BigInt(1));
    EXPECT_EQ(Rational(BigInt(6), BigInt(3)).toString(), "2");
    EXPECT_EQ(Rational(BigInt(9223372036854775807LL), BigInt(1)).toString(),
              "9223372036854775807");
    EXPECT_EQ((Rational(parse("340282366920938463463374607431768211456"),
                        parse("9223372036854775808"))).toString(),
              "36893488147419103232"); // 2^128 / 2^63 = 2^65

    expectCanonical(Rational(BigInt(-2), BigInt(4)));
    expectCanonical(Rational(parse("123456789012345678901234567890"),
                             parse("98765432109876543210")));
}

TEST(RationalConstruction, ZeroHandling)
{
    Rational z;
    EXPECT_TRUE(z.isZero());
    EXPECT_EQ(z.signum(), 0);
    EXPECT_EQ(z.toString(), "0");
    EXPECT_EQ(z.num(), BigInt(0));
    EXPECT_EQ(z.den(), BigInt(1));
}

TEST(RationalParse, ValidAndInvalid)
{
    Rational v;
    EXPECT_TRUE(Rational::tryParse(v, "-3/4"));
    EXPECT_EQ(v, Rational(BigInt(-3), BigInt(4)));
    EXPECT_TRUE(Rational::tryParse(v, "007"));
    EXPECT_EQ(v, Rational(7));
    EXPECT_TRUE(Rational::tryParse(v, "-2/4"));
    EXPECT_EQ(v, parseR("-1/2"));
    EXPECT_FALSE(Rational::tryParse(v, ""));
    EXPECT_FALSE(Rational::tryParse(v, "3/0"));
    EXPECT_FALSE(Rational::tryParse(v, "1/"));
    EXPECT_FALSE(Rational::tryParse(v, "/2"));
    EXPECT_FALSE(Rational::tryParse(v, "1/2/3"));
    EXPECT_FALSE(Rational::tryParse(v, "a/b"));
    EXPECT_FALSE(Rational::tryParse(v, "3/-4")); // denominator must be unsigned
}

TEST(RationalFixed, PythonOracleVectors)
{
    for (const BinCase &c : kCases) {
        const Rational a = parseR(c.a);
        const Rational b = parseR(c.b);
        ASSERT_EQ((a + b).toString(), c.sum) << "a=" << c.a << " b=" << c.b;
        ASSERT_EQ((a - b).toString(), c.diff) << "a=" << c.a << " b=" << c.b;
        ASSERT_EQ((a * b).toString(), c.prod) << "a=" << c.a << " b=" << c.b;
        ASSERT_EQ((a / b).toString(), c.quot) << "a=" << c.a << " b=" << c.b;
    }
}

TEST(RationalProperty, FieldAxioms)
{
    std::uint64_t state = 0x51ED270B4C9E1DBFULL;
    for (int iter = 0; iter < 20000; ++iter) {
        const Rational a = randomRational(state, 3);
        const Rational b = randomRational(state, 3);
        const Rational c = randomRational(state, 3);

        expectCanonical(a);
        expectCanonical(b);

        EXPECT_EQ(a + b, b + a);
        EXPECT_EQ(a * b, b * a);
        EXPECT_EQ((a + b) + c, a + (b + c));
        EXPECT_EQ((a + b) - b, a);
        EXPECT_EQ(a - a, Rational(0));
        EXPECT_EQ(a * (b + c), a * b + a * c);
        EXPECT_EQ(a * Rational(1), a);
        EXPECT_EQ(a * Rational(0), Rational(0));
        EXPECT_EQ(-(-a), a);
        if (!b.isZero()) {
            EXPECT_EQ((a / b) * b, a);
        }
        EXPECT_EQ(a == b, !(a < b) && !(a > b));
        EXPECT_EQ(a < b, b > a);
        EXPECT_EQ(a <= b, (a < b) || (a == b));
        expectCanonical(a + b);
        expectCanonical(a * b);
        if (!b.isZero())
            expectCanonical(a / b);
    }
}

TEST(RationalProperty, SmallRangeAgainstInt64)
{
    std::uint64_t state = 0x0F1E2D3C4B5A6978ULL;
    for (int iter = 0; iter < 20000; ++iter) {
        const std::int64_t an = static_cast<std::int64_t>(nextU64(state) % 2000) - 1000;
        const std::int64_t ad = static_cast<std::int64_t>(nextU64(state) % 2000) + 1;
        const std::int64_t bn = static_cast<std::int64_t>(nextU64(state) % 2000) - 1000;
        const std::int64_t bd = static_cast<std::int64_t>(nextU64(state) % 2000) + 1;

        const Rational a(an, ad);
        const Rational b(bn, bd);

        // Exact int64 oracle: cross-multiplied sums/products stay in range.
        const std::int64_t sumN = an * bd + bn * ad;
        const std::int64_t sumD = ad * bd;
        const std::int64_t g = std::gcd(sumN, sumD); // gcd of absolutes
        EXPECT_EQ(a + b, Rational(BigInt(sumN / g), BigInt(sumD / g)));

        EXPECT_EQ(a < b, an * static_cast<std::int64_t>(bd) <
                             bn * static_cast<std::int64_t>(ad));
    }
}

TEST(RationalProperty, StringRoundTrip)
{
    std::uint64_t state = 0x13579BDF2468ACE0ULL;
    for (int iter = 0; iter < 10000; ++iter) {
        const Rational a = randomRational(state, 4);
        Rational back;
        ASSERT_TRUE(Rational::tryParse(back, a.toString()));
        ASSERT_EQ(back, a);
    }
}

TEST(RationalFits, Int64Boundary)
{
    std::int64_t out = 0;
    EXPECT_TRUE(Rational(42).fitsInt64(out));
    EXPECT_EQ(out, 42);
    EXPECT_TRUE(parseR("-9223372036854775808").fitsInt64(out));
    EXPECT_EQ(out, std::numeric_limits<std::int64_t>::min());
    EXPECT_FALSE(parseR("1/2").fitsInt64(out));
    EXPECT_FALSE(parseR("9223372036854775808").fitsInt64(out));
    EXPECT_EQ(Rational(std::numeric_limits<std::int64_t>::min()).toString(),
              "-9223372036854775808");
}
