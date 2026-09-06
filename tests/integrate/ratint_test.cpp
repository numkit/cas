#include <numkit/cas/integrate/ratint.hpp>

#include <gtest/gtest.h>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Ctx;
using numkit::cas::Expr;
using numkit::cas::NodeKind;
using numkit::cas::Rational;
using numkit::cas::UPoly;

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

Rational rr(std::uint64_t &state, int range)
{
    const std::int64_t n = static_cast<std::int64_t>(nextU64(state) % (2 * range + 1)) - range;
    const std::int64_t d =
        nextU64(state) % 3 == 0 ? static_cast<std::int64_t>(nextU64(state) % 4 + 1) : 1;
    return Rational(BigInt(n), BigInt(d));
}

struct RatIntTest : public ::testing::Test
{
    Ctx c;
    Expr x;

    void SetUp() override { x = c.symbol("x"); }

    UPoly P(const std::string &csv)
    {
        std::vector<Rational> cs;
        std::size_t pos = 0;
        while (pos <= csv.size()) {
            const std::size_t comma = csv.find(',', pos);
            const std::string tok =
                csv.substr(pos, comma == std::string::npos ? std::string::npos
                                                           : comma - pos);
            Rational r;
            if (!Rational::tryParse(r, tok))
                ADD_FAILURE() << "bad coeff: " << tok;
            cs.push_back(r);
            if (comma == std::string::npos)
                break;
            pos = comma + 1;
        }
        return UPoly(std::move(cs));
    }

    Expr build(const UPoly &num, const UPoly &den)
    {
        if (den.isConst() && den.coeff(0) == Rational(std::int64_t{1}))
            return numkit::cas::toExpr(c, num, x);
        return c.mul({numkit::cas::toExpr(c, num, x),
                      c.pow(numkit::cas::toExpr(c, den, x),
                            c.number(std::int64_t{-1}))});
    }

    // d(Rn/Rd) + g/S == N/D in Q(x):
    // (dn*S + gn*dd) * D == N * dd * S.
    bool hermiteIdentity(const numkit::cas::HermiteResult &h,
                         const UPoly &N, const UPoly &D)
    {
        const UPoly dn = h.rn.derivative() * h.rd - h.rn * h.rd.derivative();
        const UPoly dd = h.rd * h.rd;
        return (dn * h.S + h.gn * dd) * D == dd * h.S * N;
    }
};

} // namespace

TEST_F(RatIntTest, ToRationalExtraction)
{
    UPoly n, d;
    EXPECT_TRUE(numkit::cas::toRational(c, x, x, n, d));
    EXPECT_EQ(n, P("0,1"));
    EXPECT_EQ(d, P("1"));

    const Expr e = c.mul({c.number(std::int64_t{3}),
                          c.pow(c.add({x, c.number(std::int64_t{1})}),
                                c.number(std::int64_t{-2}))});
    EXPECT_TRUE(numkit::cas::toRational(c, e, x, n, d));
    // 3/(x+1)^2: num = 3, den = (x+1)^2 = 1,2,1
    EXPECT_EQ(n * d, P("3") * P("1,2,1"));

    EXPECT_FALSE(numkit::cas::toRational(c, c.func("sin", x), x, n, d));
    EXPECT_FALSE(numkit::cas::toRational(c, c.symbol("y"), x, n, d));
    EXPECT_FALSE(numkit::cas::toRational(
        c, c.pow(x, c.number(Rational(std::int64_t{1}, BigInt(2)))), x, n, d));
}

TEST_F(RatIntTest, ToRationalRoundTrip)
{
    std::uint64_t state = 0x51ED270B4C9E1DBFULL;
    for (int iter = 0; iter < 3000; ++iter) {
        const int dn = static_cast<int>(nextU64(state) % 4);
        const int dd = static_cast<int>(nextU64(state) % 3);
        std::vector<Rational> nc, dc{Rational(std::int64_t{1})};
        for (int i = 0; i <= dn; ++i)
            nc.push_back(rr(state, 6));
        for (int i = 1; i <= dd; ++i)
            dc.push_back(rr(state, 6));
        UPoly den(dc);
        if (den.isZero())
            continue;
        const UPoly num(nc);

        const Expr e = build(num, den);
        UPoly n2, d2;
        ASSERT_TRUE(numkit::cas::toRational(c, e, x, n2, d2))
            << c.toString(numkit::cas::toExpr(c, num, x)) << " / "
            << c.toString(numkit::cas::toExpr(c, den, x));
        ASSERT_EQ(n2 * den, num * d2) << "fraction equality after round trip";
    }
}

TEST_F(RatIntTest, HermiteProperty)
{
    std::uint64_t state = 0x0BADC0DE5AFE1234ULL;
    for (int iter = 0; iter < 3000; ++iter) {
        const int dn = static_cast<int>(nextU64(state) % 4);
        const int dd = 1 + static_cast<int>(nextU64(state) % 5);
        std::vector<Rational> nc, dc;
        for (int i = 0; i <= dn; ++i)
            nc.push_back(rr(state, 6));
        for (int i = 0; i < dd; ++i)
            dc.push_back(rr(state, 5));
        UPoly num(nc), den(dc);
        if (den.isZero())
            continue;

        const numkit::cas::HermiteResult h = numkit::cas::hermiteReduce(num, den);
        ASSERT_TRUE(hermiteIdentity(h, num, den))
            << "N=" << num.toString() << " D=" << den.toString();
        ASSERT_TRUE(h.S.isZero() ||
                    numkit::cas::UPoly::gcd(h.S, h.S.derivative()).isConst())
            << "S not squarefree: " << h.S.toString();
        ASSERT_TRUE(h.gn.isZero() || h.gn.deg() < h.S.deg())
            << "residual not proper";
    }
}

namespace {

// Random denominator factored into linear factors (rational roots) and
// irreducible quadratics with square 4c-b^2, with multiplicities —
// the M0 full-integration scope.
UPoly randomDenominator(std::uint64_t &state)
{
    UPoly d(Rational(std::int64_t{1}));
    const int lin = static_cast<int>(nextU64(state) % 3);
    const int quad = static_cast<int>(nextU64(state) % 2);
    for (int i = 0; i < lin; ++i) {
        const Rational r = rr(state, 6);
        const int m = 1 + static_cast<int>(nextU64(state) % 3);
        d = d * UPoly(std::vector<Rational>{Rational(-r), Rational(std::int64_t{1})}).powUInt(m);
    }
    for (int i = 0; i < quad; ++i) {
        const Rational b = rr(state, 4);
        const Rational s = rr(state, 4).abs();
        if (s.isZero())
            continue;
        // x^2 + b x + (b^2 + s^2)/4 has 4c - b^2 = s^2.
        const Rational c0 = (b * b + s * s) / Rational(std::int64_t{4});
        const int m = 1 + static_cast<int>(nextU64(state) % 3);
        d = d * UPoly(std::vector<Rational>{c0, b, Rational(std::int64_t{1})}).powUInt(m);
    }
    return d;
}

} // namespace

TEST_F(RatIntTest, FullIntegrationDoD)
{
    std::uint64_t state = 0xFEEDFACE0DDBEAULL;
    for (int iter = 0; iter < 2000; ++iter) {
        UPoly den = randomDenominator(state);
        if (den.isConst() || den.isZero())
            continue;
        const int nn = static_cast<int>(nextU64(state) % den.deg());
        std::vector<Rational> nc;
        for (int i = 0; i <= nn; ++i)
            nc.push_back(rr(state, 6));
        UPoly num(nc);
        if (num.isZero())
            continue;

        const Expr f = build(num, den);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        if (!r.proved()) {
            std::string yun;
            for (const UPoly &F : den.squarefreeDecomposition())
                yun += " | " + F.toString();
            ADD_FAILURE() << "iter " << iter << " reason=" << r.reason
                          << " f=" << c.toString(f) << " yun:" << yun;
            return;
        }
        ASSERT_FALSE(r.F.isNull());
    }
}

TEST_F(RatIntTest, FixedDemos)
{
    auto integrate = [&](const std::string &numCsv, const std::string &denCsv) {
        const Expr f = build(P(numCsv), P(denCsv));
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        EXPECT_TRUE(r.proved()) << r.reason;
        return r.proved() ? c.toString(r.F) : std::string("<failed>");
    };

    // ∫ dx/(x^2+1) = atan(x)
    EXPECT_EQ(integrate("1", "1,0,1"), "atan(x)");
    // ∫ x dx/(x^2+1) = (1/2) log(1 + x^2)
    EXPECT_EQ(integrate("0,1", "1,0,1"), "1/2*log(1 + x^2)");
    // ∫ dx/(x^3+x) = log(x) - (1/2) log(1 + x^2)
    EXPECT_EQ(integrate("1", "0,1,0,1"), "log(x) + -1/2*log(1 + x^2)");
    // ∫ dx/(x^2+1)^2 = x/(2(x^2+1)) + atan(x)/2
    EXPECT_EQ(integrate("1", "1,0,2,0,1"), "1/2*x*(1 + x^2)^-1 + 1/2*atan(x)");
    // ∫ x^3 dx = x^4/4
    EXPECT_EQ(integrate("0,0,0,1", "1"), "1/4*x^4");
    // ∫ dx/(4x^2+1) = atan(2x)/2
    EXPECT_EQ(integrate("1", "1,0,4"), "1/2*atan(2*x)");
}

TEST_F(RatIntTest, HonestFailures)
{
    numkit::cas::RationalIntegral r;

    // Not rational in x.
    r = numkit::cas::integrateRational(c, c.func("sin", x), x);
    EXPECT_FALSE(r.proved());
    EXPECT_FALSE(r.reason.empty());

    // Irreducible cubic factor (x^3+2 has no rational root).
    r = numkit::cas::integrateRational(
        c, build(P("1"), P("2,0,0,1")), x);
    EXPECT_FALSE(r.proved());

    // Quadratic with non-square 4c-b^2: x^2+2 -> needs sqrt(8).
    r = numkit::cas::integrateRational(
        c, build(P("1"), P("2,0,1")), x);
    EXPECT_FALSE(r.proved());
}

TEST_F(RatIntTest, CertificateCatchesNothingOnZero)
{
    const numkit::cas::RationalIntegral r =
        numkit::cas::integrateRational(c, c.zero(), x);
    EXPECT_TRUE(r.proved());
    EXPECT_EQ(c.toString(r.F), "0");
}
