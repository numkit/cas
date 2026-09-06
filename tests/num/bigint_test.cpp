#include <numkit/cas/num/bigint.hpp>

#include <limits>

#include <gtest/gtest.h>
#include "test_util.hpp"

namespace {

using cas_test::nextU64;
using cas_test::parse;
using cas_test::randomBig;
using numkit::cas::BigInt;

// Python-generated oracle vectors: a, b, a+b, a-b, a*b, a/b (trunc), a%b.
struct BinCase
{
    const char *a;
    const char *b;
    const char *sum;
    const char *diff;
    const char *prod;
    const char *quot;
    const char *rem;
};

const BinCase kCases[] = {
    {"0", "1", "1", "-1", "0", "0", "0"},
    {"0", "-1", "-1", "1", "0", "0", "0"},
    {"0", "2", "2", "-2", "0", "0", "0"},
    {"0", "18446744073709551615", "18446744073709551615", "-18446744073709551615", "0", "0", "0"},
    {"0", "-1000000000000000000", "-1000000000000000000", "1000000000000000000", "0", "0", "0"},
    {"1", "1", "2", "0", "1", "1", "0"},
    {"1", "-1", "0", "2", "-1", "-1", "0"},
    {"1", "2", "3", "-1", "2", "0", "1"},
    {"1", "18446744073709551615", "18446744073709551616", "-18446744073709551614", "18446744073709551615", "0", "1"},
    {"1", "-1000000000000000000", "-999999999999999999", "1000000000000000001", "-1000000000000000000", "0", "1"},
    {"-1", "1", "0", "-2", "-1", "-1", "0"},
    {"-1", "-1", "-2", "0", "1", "1", "0"},
    {"-1", "2", "1", "-3", "-2", "0", "-1"},
    {"-1", "18446744073709551615", "18446744073709551614", "-18446744073709551616", "-18446744073709551615", "0", "-1"},
    {"-1", "-1000000000000000000", "-1000000000000000001", "999999999999999999", "1000000000000000000", "0", "-1"},
    {"2", "1", "3", "1", "2", "2", "0"},
    {"2", "-1", "1", "3", "-2", "-2", "0"},
    {"2", "2", "4", "0", "4", "1", "0"},
    {"2", "18446744073709551615", "18446744073709551617", "-18446744073709551613", "36893488147419103230", "0", "2"},
    {"2", "-1000000000000000000", "-999999999999999998", "1000000000000000002", "-2000000000000000000", "0", "2"},
    {"-2", "1", "-1", "-3", "-2", "-2", "0"},
    {"-2", "-1", "-3", "-1", "2", "2", "0"},
    {"-2", "2", "0", "-4", "-4", "-1", "0"},
    {"-2", "18446744073709551615", "18446744073709551613", "-18446744073709551617", "-36893488147419103230", "0", "-2"},
    {"-2", "-1000000000000000000", "-1000000000000000002", "999999999999999998", "2000000000000000000", "0", "-2"},
    {"3", "1", "4", "2", "3", "3", "0"},
    {"3", "-1", "2", "4", "-3", "-3", "0"},
    {"3", "2", "5", "1", "6", "1", "1"},
    {"3", "18446744073709551615", "18446744073709551618", "-18446744073709551612", "55340232221128654845", "0", "3"},
    {"3", "-1000000000000000000", "-999999999999999997", "1000000000000000003", "-3000000000000000000", "0", "3"},
    {"10", "1", "11", "9", "10", "10", "0"},
    {"10", "-1", "9", "11", "-10", "-10", "0"},
    {"10", "2", "12", "8", "20", "5", "0"},
    {"10", "18446744073709551615", "18446744073709551625", "-18446744073709551605", "184467440737095516150", "0", "10"},
    {"10", "-1000000000000000000", "-999999999999999990", "1000000000000000010", "-10000000000000000000", "0", "10"},
    {"18446744073709551615", "1", "18446744073709551616", "18446744073709551614", "18446744073709551615", "18446744073709551615", "0"},
    {"18446744073709551615", "-1", "18446744073709551614", "18446744073709551616", "-18446744073709551615", "-18446744073709551615", "0"},
    {"18446744073709551615", "2", "18446744073709551617", "18446744073709551613", "36893488147419103230", "9223372036854775807", "1"},
    {"18446744073709551615", "18446744073709551615", "36893488147419103230", "0", "340282366920938463426481119284349108225", "1", "0"},
    {"18446744073709551615", "-1000000000000000000", "17446744073709551615", "19446744073709551615", "-18446744073709551615000000000000000000", "-18", "446744073709551615"},
    {"-33277630584557368168641179782175934609", "-18446744073709551616", "-33277630584557368187087923855885486225", "-33277630584557368150194435708466382993", "613863934772779353151284252839347662430395784855126278144", "1803983968747358271", "-8401620442256918673"},
    {"3", "1000000000000000000", "1000000000000000003", "-999999999999999997", "3000000000000000000", "0", "3"},
    {"18446744073709551615", "10", "18446744073709551625", "18446744073709551605", "184467440737095516150", "1844674407370955161", "5"},
    {"19307456724411717564186006731576660436", "-243584933552624990812409226541457368589", "-224277476828213273248223219809880708153", "262892390277036708376595233273034029025", "-4703005563286010782226185808001749628641216445850908017090921550804945444804", "0", "19307456724411717564186006731576660436"},
    {"-17931349239164317148", "-243584933552624990812409226541457368589", "-243584933552624990830340575780621685737", "243584933552624990794477877302293051441", "4367806512930752877033613022504561475313485832341129264172", "0", "-17931349239164317148"},
    {"1000000000000000000", "330396923463687876920955548412152318180", "330396923463687876921955548412152318180", "-330396923463687876919955548412152318180", "330396923463687876920955548412152318180000000000000000000", "0", "1000000000000000000"},
    {"330396923463687876920955548412152318180", "-1", "330396923463687876920955548412152318179", "330396923463687876920955548412152318181", "-330396923463687876920955548412152318180", "-330396923463687876920955548412152318180", "0"},
    {"9223372036854775807", "10", "9223372036854775817", "9223372036854775797", "92233720368547758070", "922337203685477580", "7"},
    {"123456789012345678901234567890", "-9876543210", "123456789012345678891358024680", "123456789012345678911111111100", "-1219326311248285321124828532111263526900", "-12499999887343749990", "1562499990"},
    {"-340282366920938463463374607431768211456", "18446744073709551616", "-340282366920938463444927863358058659840", "-340282366920938463481821351505477763072", "-6277101735386680763835789423207666416102355444464034512896", "-18446744073709551616", "0"},
};

} // namespace

TEST(BigIntConstruction, Basics)
{
    EXPECT_EQ(BigInt().toString(), "0");
    EXPECT_EQ(BigInt(std::int64_t{0}).toString(), "0");
    EXPECT_EQ(BigInt(std::int64_t{1}).toString(), "1");
    EXPECT_EQ(BigInt(std::int64_t{-1}).toString(), "-1");
    EXPECT_EQ(BigInt(std::int64_t{9223372036854775807LL}).toString(), "9223372036854775807");
    EXPECT_EQ(BigInt(std::int64_t{-9223372036854775807LL - 1}).toString(), "-9223372036854775808");
    EXPECT_EQ(BigInt(std::uint64_t{18446744073709551615ULL}).toString(), "18446744073709551615");
    EXPECT_TRUE(BigInt().isZero());
    EXPECT_EQ(BigInt().signum(), 0);
    EXPECT_EQ(BigInt(-5).signum(), -1);
    EXPECT_EQ(BigInt(5).signum(), 1);
}

TEST(BigIntConstruction, BitLength)
{
    EXPECT_EQ(BigInt().bitLength(), 0u);
    EXPECT_EQ(BigInt(1).bitLength(), 1u);
    EXPECT_EQ(BigInt(255).bitLength(), 8u);
    EXPECT_EQ(BigInt(256).bitLength(), 9u);
    EXPECT_EQ(parse("18446744073709551616").bitLength(), 65u); // 2^64
}

TEST(BigIntParse, ValidAndInvalid)
{
    BigInt v;
    EXPECT_TRUE(BigInt::tryParse(v, "0"));
    EXPECT_EQ(v.toString(), "0");
    EXPECT_TRUE(BigInt::tryParse(v, "007"));
    EXPECT_EQ(v.toString(), "7");
    EXPECT_TRUE(BigInt::tryParse(v, "+7"));
    EXPECT_EQ(v.toString(), "7");
    EXPECT_TRUE(BigInt::tryParse(v, "-9223372036854775808"));
    EXPECT_EQ(v, BigInt(std::numeric_limits<std::int64_t>::min()));
    EXPECT_FALSE(BigInt::tryParse(v, ""));
    EXPECT_FALSE(BigInt::tryParse(v, "-"));
    EXPECT_FALSE(BigInt::tryParse(v, "12a"));
    EXPECT_FALSE(BigInt::tryParse(v, " 12"));
    EXPECT_FALSE(BigInt::tryParse(v, "1 2"));
}

TEST(BigIntFixed, PythonOracleVectors)
{
    for (const BinCase &c : kCases) {
        const BigInt a = parse(c.a);
        const BigInt b = parse(c.b);
        ASSERT_EQ((a + b).toString(), c.sum) << "a=" << c.a << " b=" << c.b;
        ASSERT_EQ((a - b).toString(), c.diff) << "a=" << c.a << " b=" << c.b;
        ASSERT_EQ((a * b).toString(), c.prod) << "a=" << c.a << " b=" << c.b;
        ASSERT_EQ((a / b).toString(), c.quot) << "a=" << c.a << " b=" << c.b;
        ASSERT_EQ((a % b).toString(), c.rem) << "a=" << c.a << " b=" << c.b;
    }
}

TEST(BigIntProperty, AlgebraInvariants)
{
    std::uint64_t state = 0x9E3779B97F4A7C15ULL;
    for (int iter = 0; iter < 50000; ++iter) {
        const BigInt a = randomBig(state, 4);
        const BigInt b = randomBig(state, 4);

        EXPECT_EQ(a + b, b + a);
        EXPECT_EQ(a * b, b * a);
        EXPECT_EQ((a + b) - b, a);
        EXPECT_EQ(a - a, BigInt(0));
        if (!b.isZero())
            EXPECT_EQ(b * (a / b) + a % b, a);
        EXPECT_EQ(a + BigInt(0), a);
        EXPECT_EQ(a * BigInt(1), a);
        EXPECT_EQ(a * BigInt(0), BigInt(0));
        EXPECT_EQ(-(-a), a);
        EXPECT_EQ(a.abs(), (a < BigInt(0) ? -a : a));
    }
}

TEST(BigIntProperty, TruncDivisionInvariants)
{
    std::uint64_t state = 0xC0FFEE123456789ULL;
    for (int iter = 0; iter < 50000; ++iter) {
        const BigInt a = randomBig(state, 4);
        BigInt b = randomBig(state, 3);
        if (b.isZero())
            b = BigInt(1);

        BigInt q, r;
        BigInt::divMod(a, b, q, r);
        ASSERT_EQ(q * b + r, a);
        ASSERT_TRUE(r.abs() < b.abs()) << "a=" << a.toString() << " b=" << b.toString();
        ASSERT_TRUE(r.isZero() || r.signum() == a.signum())
            << "a=" << a.toString() << " b=" << b.toString();
        ASSERT_TRUE(q.isZero() ||
                    q.signum() == ((a.signum() < 0) != (b.signum() < 0) ? -1 : 1))
            << "a=" << a.toString() << " b=" << b.toString();
    }
}

TEST(BigIntProperty, SmallRangeAgainstInt64)
{
    std::uint64_t state = 0xDEADBEEFCAFEBABEULL;
    for (int iter = 0; iter < 50000; ++iter) {
        const std::int64_t av = static_cast<std::int64_t>(nextU64(state) % (1 << 24)) - (1 << 23);
        const std::int64_t bv = static_cast<std::int64_t>(nextU64(state) % (1 << 24)) - (1 << 23);
        const BigInt a(av);
        const BigInt b(bv);

        EXPECT_EQ(a + b, BigInt(av + bv));
        EXPECT_EQ(a - b, BigInt(av - bv));
        EXPECT_EQ(a * b, BigInt(av * bv));
        if (bv != 0) {
            EXPECT_EQ(a / b, BigInt(av / bv));
            EXPECT_EQ(a % b, BigInt(av % bv));
        }
        EXPECT_EQ(a < b, av < bv);
        EXPECT_EQ(a == b, av == bv);
    }
}

TEST(BigIntProperty, StringRoundTrip)
{
    std::uint64_t state = 0x1234567890ABCDEFULL;
    for (int iter = 0; iter < 50000; ++iter) {
        const BigInt a = randomBig(state, 5);
        BigInt back;
        ASSERT_TRUE(BigInt::tryParse(back, a.toString()));
        ASSERT_EQ(back, a);
    }
}

TEST(BigIntShift, BasicsAndFloorSemantics)
{
    EXPECT_EQ((BigInt(1) << 64).toString(), "18446744073709551616");
    EXPECT_EQ((BigInt(1) << 128).toString(), "340282366920938463463374607431768211456");
    EXPECT_EQ((BigInt(-1) << 64).toString(), "-18446744073709551616");

    EXPECT_EQ(BigInt(-3) >> 1, BigInt(-2)); // floor(-1.5) = -2
    EXPECT_EQ(BigInt(-4) >> 1, BigInt(-2));
    EXPECT_EQ(BigInt(-2) >> 64, BigInt(-1));
    EXPECT_EQ(BigInt(-1) >> 100, BigInt(-1));
    EXPECT_EQ(BigInt(3) >> 1, BigInt(1));
    EXPECT_EQ(BigInt(0) >> 7, BigInt(0));

    std::uint64_t state = 0xFEEDFACEULL;
    for (int iter = 0; iter < 50000; ++iter) {
        const BigInt a = randomBig(state, 3).abs();
        const std::size_t sh = static_cast<std::size_t>(nextU64(state) % 200);
        EXPECT_EQ((a << sh) >> sh, a);
    }
}

TEST(BigIntGcd, FixedAndProperties)
{
    EXPECT_EQ(BigInt::gcd(BigInt(48), BigInt(18)), BigInt(6));
    EXPECT_EQ(BigInt::gcd(BigInt(-48), BigInt(18)), BigInt(6));
    EXPECT_EQ(BigInt::gcd(BigInt(0), BigInt(5)), BigInt(5));
    EXPECT_EQ(BigInt::gcd(BigInt(0), BigInt(0)), BigInt(0));
    EXPECT_EQ(BigInt::gcd(BigInt(0), BigInt(-5)), BigInt(5));
    EXPECT_EQ(BigInt::gcd(parse("18446744073709551616"), parse("9223372036854775808")), BigInt(9223372036854775808ULL));
    EXPECT_EQ(BigInt::gcd(parse("123456789012345678901234567890"), parse("987654321098765432109876543210")),
              parse("9000000000900000000090"));

    std::uint64_t state = 0xABCDEF01ULL;
    for (int iter = 0; iter < 5000; ++iter) {
        const BigInt a = randomBig(state, 3);
        const BigInt b = randomBig(state, 3);
        const BigInt g = BigInt::gcd(a, b);
        if (!a.isZero())
            EXPECT_EQ(a % g, BigInt(0));
        if (!b.isZero())
            EXPECT_EQ(b % g, BigInt(0));
        EXPECT_FALSE(g.isNegative());
    }
}

TEST(BigIntFits, Int64Uint64Boundaries)
{
    std::int64_t i64 = 0;
    std::uint64_t u64 = 0;

    EXPECT_TRUE(BigInt(0).fitsInt64(i64));
    EXPECT_EQ(i64, 0);
    EXPECT_TRUE(BigInt(std::numeric_limits<std::int64_t>::min()).fitsInt64(i64));
    EXPECT_EQ(i64, std::numeric_limits<std::int64_t>::min());
    EXPECT_TRUE(BigInt(std::numeric_limits<std::int64_t>::max()).fitsInt64(i64));
    EXPECT_EQ(i64, std::numeric_limits<std::int64_t>::max());
    EXPECT_FALSE(parse("9223372036854775808").fitsInt64(i64));  // 2^63 positive
    EXPECT_FALSE(parse("-9223372036854775809").fitsInt64(i64));

    EXPECT_TRUE(BigInt(std::numeric_limits<std::uint64_t>::max()).fitsUint64(u64));
    EXPECT_EQ(u64, std::numeric_limits<std::uint64_t>::max());
    EXPECT_FALSE(parse("18446744073709551616").fitsUint64(u64)); // 2^64
    EXPECT_FALSE(BigInt(-1).fitsUint64(u64));
}
