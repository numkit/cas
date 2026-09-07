#include <numkit/cas/poly/modcpoly.hpp>

#include <gtest/gtest.h>

namespace {

using numkit::cas::BigInt;
using numkit::cas::ModCPoly;
using numkit::cas::ModCRing;
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

// Ascending rational csv -> UPoly.
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

std::string S(const UPoly &p)
{
    std::string out;
    for (const Rational &c : p.coeffs()) {
        if (!out.empty())
            out += ",";
        out += c.toString();
    }
    return out;
}

ModCPoly MP(const ModCRing &ring, const std::string &spec)
{
    // "p0|p1|..." with each pi an ascending rational csv ("-" = zero poly).
    std::vector<UPoly> cs;
    std::size_t pos = 0;
    while (pos <= spec.size()) {
        const std::size_t bar = spec.find('|', pos);
        const std::string tok =
            spec.substr(pos, bar == std::string::npos ? std::string::npos
                                                      : bar - pos);
        cs.push_back(tok == "-" ? UPoly() : P(tok));
        if (bar == std::string::npos)
            break;
        pos = bar + 1;
    }
    return ModCPoly(ring, std::move(cs));
}

// Python oracle (exact Fraction algebra in Q[t]/(c)): c, a, b,
// a+b, a*b, a^-1 (all elements as ascending csv, degree < deg c).
struct Case
{
    const char *c;
    const char *a;
    const char *b;
    const char *sum;
    const char *prod;
    const char *inva;
};

const Case kCases[] = {
    {"-2,0,1", "3,1", "3,1", "6,2", "11,6", "3/7,-1/7"},
    {"-2,0,1", "3,1", "5,-2", "8,-1", "11,-1", "3/7,-1/7"},
    {"-2,0,1", "3,1", "-1/2,3/4", "5/2,7/4", "0,7/4", "3/7,-1/7"},
    {"-2,0,1", "5,-2", "3,1", "8,-1", "11,-1", "5/17,2/17"},
    {"-2,0,1", "5,-2", "5,-2", "10,-4", "33,-20", "5/17,2/17"},
    {"-2,0,1", "5,-2", "-1/2,3/4", "9/2,-5/4", "-11/2,19/4", "5/17,2/17"},
    {"-2,0,1", "-1/2,3/4", "3,1", "5/2,7/4", "0,7/4", "4/7,6/7"},
    {"-2,0,1", "-1/2,3/4", "5,-2", "9/2,-5/4", "-11/2,19/4", "4/7,6/7"},
    {"-2,0,1", "-1/2,3/4", "-1/2,3/4", "-1,3/2", "11/8,-3/4", "4/7,6/7"},
    {"-2,0,1", "0,1", "3,1", "3,2", "2,3", "0,1/2"},
    {"-2,0,1", "0,1", "5,-2", "5,-1", "-4,5", "0,1/2"},
    {"-2,0,1", "0,1", "-1/2,3/4", "-1/2,7/4", "3/2,-1/2", "0,1/2"},
    {"-2,0,1", "7,0", "3,1", "10,1", "21,7", "1/7,0"},
    {"-2,0,1", "7,0", "5,-2", "12,-2", "35,-14", "1/7,0"},
    {"-2,0,1", "7,0", "-1/2,3/4", "13/2,3/4", "-7/2,21/4", "1/7,0"},
    {"1,1,1", "3,1", "3,1", "6,2", "8,5", "2/7,-1/7"},
    {"1,1,1", "3,1", "5,-2", "8,-1", "17,1", "2/7,-1/7"},
    {"1,1,1", "3,1", "-1/2,3/4", "5/2,7/4", "-9/4,1", "2/7,-1/7"},
    {"1,1,1", "5,-2", "3,1", "8,-1", "17,1", "7/39,2/39"},
    {"1,1,1", "5,-2", "5,-2", "10,-4", "21,-24", "7/39,2/39"},
    {"1,1,1", "5,-2", "-1/2,3/4", "9/2,-5/4", "-1,25/4", "7/39,2/39"},
    {"1,1,1", "-1/2,3/4", "3,1", "5/2,7/4", "-9/4,1", "-20/19,-12/19"},
    {"1,1,1", "-1/2,3/4", "5,-2", "9/2,-5/4", "-1,25/4", "-20/19,-12/19"},
    {"1,1,1", "-1/2,3/4", "-1/2,3/4", "-1,3/2", "-5/16,-21/16", "-20/19,-12/19"},
    {"1,1,1", "0,1", "3,1", "3,2", "-1,2", "-1,-1"},
    {"1,1,1", "0,1", "5,-2", "5,-1", "2,7", "-1,-1"},
    {"1,1,1", "0,1", "-1/2,3/4", "-1/2,7/4", "-3/4,-5/4", "-1,-1"},
    {"1,1,1", "7,0", "3,1", "10,1", "21,7", "1/7,0"},
    {"1,1,1", "7,0", "5,-2", "12,-2", "35,-14", "1/7,0"},
    {"1,1,1", "7,0", "-1/2,3/4", "13/2,3/4", "-7/2,21/4", "1/7,0"},
};

} // namespace

TEST(ModCRingFixed, PythonOracle)
{
    for (const Case &k : kCases) {
        const ModCRing ring(P(k.c));
        const UPoly a = ring.reduce(P(k.a));
        const UPoly b = ring.reduce(P(k.b));
        EXPECT_EQ(S(ring.add(a, b)), k.sum) << k.c << " a=" << k.a << " b=" << k.b;
        EXPECT_EQ(S(ring.mul(a, b)), k.prod) << k.c << " a=" << k.a << " b=" << k.b;
        EXPECT_EQ(S(ring.mul(a, ring.inv(a))), "1") << k.c << " a=" << k.a;
        EXPECT_EQ(S(ring.inv(a)), S(P(k.inva))) << k.c << " a=" << k.a;
    }
}

TEST(ModCRingBoundary, LinearModulusIsQ)
{
    // c = t - 3: the ring degenerates to Q.
    const ModCRing ring(P("-3,1"));
    const UPoly a = ring.reduce(P("7,2")); // 7 + 2t = 13
    EXPECT_EQ(a, UPoly(Rational(std::int64_t{13})));
    EXPECT_EQ(ring.mul(a, ring.inv(a)), UPoly(Rational(std::int64_t{1})));
    // Reduction of a higher polynomial: t^2 = 3t = 9.
    EXPECT_EQ(ring.reduce(P("0,0,1")), UPoly(Rational(std::int64_t{9})));
}

TEST(ModCRingProperty, FieldAxioms)
{
    std::uint64_t state = 0x5EEDC0FFEE15A11ULL;
    const ModCRing ring(P("1,0,1")); // t^2 + 1, irreducible over Q
    for (int iter = 0; iter < 3000; ++iter) {
        const UPoly a = ring.reduce(P(std::to_string(static_cast<int>(nextU64(state) % 13) - 6) + "," +
                                      std::to_string(static_cast<int>(nextU64(state) % 13) - 6)));
        const UPoly b = ring.reduce(P(std::to_string(static_cast<int>(nextU64(state) % 13) - 6) + "," +
                                      std::to_string(static_cast<int>(nextU64(state) % 13) - 6)));
        const UPoly c = ring.reduce(P(std::to_string(static_cast<int>(nextU64(state) % 13) - 6) + "," +
                                      std::to_string(static_cast<int>(nextU64(state) % 13) - 6)));
        if (a.isZero() || b.isZero())
            continue;

        EXPECT_EQ(ring.add(a, b), ring.add(b, a));
        EXPECT_EQ(ring.mul(a, b), ring.mul(b, a));
        EXPECT_EQ(ring.mul(a, ring.add(b, c)), ring.add(ring.mul(a, b), ring.mul(a, c)));
        EXPECT_EQ(ring.mul(a, ring.inv(a)), ring.one());
        EXPECT_EQ(ring.sub(ring.add(a, b), b), a);
        EXPECT_EQ(ring.mul(ring.neg(a), b), ring.neg(ring.mul(a, b)));
        // Frobenius-like sanity for this specific ring: (p+qt)^2 reduces.
        EXPECT_EQ(ring.mul(a, a), ring.reduce(a * a));
    }
}

TEST(ModCRingProperty, QuadraticFastPathsMatchGenericReduction)
{
    // mul()/inv() take closed-form paths for quadratic moduli; sweep
    // random rational elements of BOTH oracle rings and require the
    // fast results to agree with the generic division-based reduce()
    // everywhere, plus the inverse identity with fractional entries.
    std::uint64_t state = 0x20C0FFEE0DD5EEDULL;
    const char *mods[] = {"-2,0,1", "1,1,1"};
    for (const char *mc : mods) {
        const ModCRing ring(P(mc));
        for (int iter = 0; iter < 4000; ++iter) {
            auto randElem = [&]() {
                const long p = static_cast<long>(nextU64(state) % 17) - 8;
                const long q = 1 + static_cast<long>(nextU64(state) % 5);
                const long r = static_cast<long>(nextU64(state) % 17) - 8;
                const long s = 1 + static_cast<long>(nextU64(state) % 5);
                return ring.reduce(P(std::to_string(p) + "/" + std::to_string(q) +
                                     "," + std::to_string(r) + "/" +
                                     std::to_string(s)));
            };
            const UPoly a = randElem();
            const UPoly b = randElem();
            if (a.isZero())
                continue;
            // fast mul == generic mul (reduce of the plain product)
            EXPECT_EQ(ring.mul(a, b), ring.reduce(a * b));
            // inverse identity and inv(inv(a)) == a
            EXPECT_EQ(ring.mul(a, ring.inv(a)), ring.one());
            EXPECT_EQ(ring.inv(ring.inv(a)), a);
            // zero and constant edges through the fast path
            EXPECT_TRUE(ring.mul(a, ring.zero()).isZero());
            EXPECT_EQ(ring.mul(a, ring.one()), a);
            const UPoly k = ring.reduce(P("3/7"));
            EXPECT_EQ(ring.mul(k, ring.inv(k)), ring.one());
        }
    }
}

TEST(ModCPolyProperty, RingAndDivision)
{
    std::uint64_t state = 0xABCDEF0123456789ULL;
    const ModCRing ring(P("1,0,1"));

    const auto rndElem = [&]() {
        return ring.reduce(P(std::to_string(static_cast<int>(nextU64(state) % 9) - 4) + "," +
                             std::to_string(static_cast<int>(nextU64(state) % 9) - 4)));
    };
    const auto rndPoly = [&](int maxDeg) {
        std::vector<UPoly> cs;
        const int deg = static_cast<int>(nextU64(state) % (maxDeg + 1));
        for (int i = 0; i <= deg; ++i)
            cs.push_back(rndElem());
        return ModCPoly(ring, std::move(cs));
    };

    for (int iter = 0; iter < 2000; ++iter) {
        const ModCPoly f = rndPoly(4);
        const ModCPoly g = rndPoly(3);
        const ModCPoly h = rndPoly(3);
        if (f.isZero() || g.isZero() || h.isZero())
            continue;

        EXPECT_EQ(f * g, g * f);
        EXPECT_EQ(f * (g + h), f * g + f * h);
        EXPECT_EQ((f + g) - g, f);
        const ModCPoly zero = ModCPoly::constant(ring, ring.zero());
        const ModCPoly monicF =
            f * ModCPoly::constant(ring, ring.inv(f.lc()));
        EXPECT_EQ(ModCPoly::gcd(f, zero), monicF);

        const ModCPoly gg = ModCPoly::gcd(f, g);
        if (!gg.isZero()) {
            ModCPoly q, r;
            ModCPoly::divMod(f, gg, q, r);
            ASSERT_TRUE(r.isZero()) << "gcd does not divide f";
            ModCPoly::divMod(g, gg, q, r);
            ASSERT_TRUE(r.isZero()) << "gcd does not divide g";
        }
        ModCPoly q, r;
        const ModCPoly d = g + ModCPoly::constant(ring, ring.one()); // avoid zero divisor
        if (!d.isZero()) {
            ModCPoly::divMod(f, d, q, r);
            ASSERT_EQ(q * d + r, f) << "divMod invariant";
            ASSERT_TRUE(r.isZero() || r.deg() < d.deg());
        }
    }
}

TEST(ModCPolyFixed, GcdOverQuadraticField)
{
    // Over Q[t]/(t^2+1): gcd((x + t)(x + 1), (x + t)(x + 2)) = x + t.
    const ModCRing ring(P("1,0,1"));
    const UPoly t = ring.reduce(P("0,1"));
    const ModCPoly xt = ModCPoly(ring, std::vector<UPoly>{t, ring.one()});
    const ModCPoly x1 = ModCPoly(ring, std::vector<UPoly>{
                                ring.one(), ring.one()});
    const ModCPoly x2 = ModCPoly(ring, std::vector<UPoly>{
                                UPoly(Rational(std::int64_t{2})), ring.one()});
    const ModCPoly f = xt * x1;
    const ModCPoly g = xt * x2;
    const ModCPoly gg = ModCPoly::gcd(f, g);
    ASSERT_EQ(gg, xt); // already monic
}
