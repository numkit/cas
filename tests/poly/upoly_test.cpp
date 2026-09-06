#include <numkit/cas/poly/upoly.hpp>

#include <gtest/gtest.h>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Rational;
using numkit::cas::UPoly;

// Parse an ascending comma-separated coefficient list ("1,-2,3/4").
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
            ADD_FAILURE() << "bad coeff token: " << tok;
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

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

// Random polynomial, degree 0..maxDeg, mixed integer/fraction coefficients.
UPoly rndPoly(std::uint64_t &state, int maxDeg)
{
    const int deg = static_cast<int>(nextU64(state) % (maxDeg + 1));
    std::vector<Rational> cs;
    for (int i = 0; i <= deg; ++i) {
        const std::int64_t n = static_cast<std::int64_t>(nextU64(state) % 19) - 9;
        const std::int64_t d =
            (nextU64(state) % 4 == 0) ? static_cast<std::int64_t>(nextU64(state) % 4 + 1)
                                      : 1;
        cs.emplace_back(BigInt(n), BigInt(d));
    }
    return UPoly(std::move(cs));
}

// Python oracle vectors: a, b, gcd (monic), resultant.
struct Case
{
    const char *a;
    const char *b;
    const char *g;
    const char *r;
};

const Case kCases[] = {
    {"5/2,27/4,9/2", "-8,0,22,6", "2/3,1", "0"},
    {"4,9,5", "-16,-8,-6,-4,10", "1,1", "0"},
    {"42,-6,-48,12", "-14,-47,65,46,-62,12", "7/2,-1/2,-4,1", "0"},
    {"-4,28,-49,10", "-4,41/2,-49/4,-11,3", "1,-9/2,1", "0"},
    {"18,14,71/3,27,35/3,-20,3,18", "9,3,27/2,27/2", "2/3,2/9,1,1", "0"},
    {"3", "-1,3,-6,9,5", "1", "81"},
    {"-35/2,-4,3/2", "14,17/4,11/4,3/2", "7/3,1", "0"},
    {"32/3,-12,4/3", "6,4", "1", "1520/3"},
    {"5,3,4,3", "15/2,9/2,6,9/2", "5/3,1,4/3,1", "0"},
    {"27,60,35,22,24", "-12,-10,8", "3/4,1", "0"},
    {"-1/2,1,-3/2,5/4", "-4,13/2,-9,11/2,15/4", "-2/5,4/5,-6/5,1", "0"},
    {"7,-7,7", "7/3", "1", "49/9"},
    {"7,-63,0,42", "-7/3,24,-27,-14,18", "1/6,-3/2,0,1", "0"},
    {"2,17,-15/2,19/2,-69/2,27/2", "-5,-40,45", "-1/9,-8/9,1", "0"},
    {"-3,9", "-42,-24,36,-54,36", "1", "-312012"},
    {"28,63/2,-7,14", "36,121/2,83/2,89/2,3,14", "2,9/4,-1/2,1", "0"},
    {"-5/6,1/3,31/6,-31/6,-14/3,23/6,10/3", "4/3,2/3,-6,8/3", "-1/4,-1/4,1", "0"},
    {"-21/2,-15/2,-15/2,-3,9/2", "-3,12,-12,-9,12", "1", "26381781"},
    {"-24,-42,-21,-26,41,28,4", "-2,13/2,27/4,-25,-49/4,-1/4,57/4,9/2", "-2,-5/2,5/2,1", "0"},
    {"-2,5/2,-9/2,4", "4", "1", "64"},
    {"-1,-3,7,12,3", "7/2,5,-71/2,15/2,6", "-1/3,-2/3,3,1", "0"},
    {"40,5,45,45", "-48,18,-19,-23,63,36", "8/9,1/9,1,1", "0"},
    {"2", "1,7,3,2", "1", "8"},
    {"5,-7,6", "7", "1", "49"},
    {"3,8,-7,6", "3,1", "1", "-246"},
    {"2/3", "-2,-8/3,4/3,-4/3,0,2", "1", "32/243"},
    {"9/4,7/4,3/4,-5/4,7/4,-3/4,3/2", "2,0,7,1,8,-6,8", "1", "15524873939/256"},
    {"-1,-5,5", "-4,2", "1", "36"},
    {"1", "-2,-8,9", "1", "1"},
    {"7,-5,5,2,7,9,7", "-8/3,1/3", "1", "2159903/729"},
};

} // namespace

TEST(UPolyBasics, ConstructionAndDegree)
{
    EXPECT_TRUE(UPoly().isZero());
    EXPECT_EQ(UPoly().deg(), -1);
    EXPECT_EQ(UPoly(Rational(std::int64_t{5})).deg(), 0);
    EXPECT_EQ(P("1,2,3").deg(), 2);
    EXPECT_EQ(P("1,2,0").deg(), 1); // trailing zero trimmed
    EXPECT_EQ(P("0,0,0").isZero(), true);
    EXPECT_EQ(UPoly::monomial(Rational(std::int64_t{3}), 4).coeff(4),
              Rational(std::int64_t{3}));
    EXPECT_EQ(UPoly::monomial(Rational(std::int64_t{3}), 4).deg(), 4);
}

TEST(UPolyBasics, ArithmeticAndToString)
{
    EXPECT_EQ(S(P("1,2,3") + P("-1,-2,6")), "0,0,9");
    EXPECT_EQ(S(P("1,2,3") - P("1,1,1")), "0,1,2");
    EXPECT_EQ(S(P("1,2") * P("3,4")), "3,10,8");
    EXPECT_EQ(S(-P("1,-2,3")), "-1,2,-3");
    EXPECT_EQ(P("0,1").powUInt(3), P("0,0,0,1"));
    EXPECT_EQ(P("0,2").powUInt(0), UPoly(Rational(std::int64_t{1})));

    EXPECT_EQ(P("0,0,0,-3,1").toString(), "x^4 - 3*x^3");
    EXPECT_EQ(P("4,0,-3/2,1").toString(), "x^3 - 3/2*x^2 + 4");
    EXPECT_EQ(P("-2,1").toString(), "x - 2");
    EXPECT_EQ(P("5").toString(), "5");
    EXPECT_EQ(P("0,-1").toString(), "-x");
}

TEST(UPolyBasics, DerivativeAndEval)
{
    EXPECT_EQ(P("1,2,3").derivative(), P("2,6"));
    EXPECT_EQ(P("7").derivative().isZero(), true);
    EXPECT_EQ(P("0,0,0,1").derivative(), P("0,0,3"));
    EXPECT_EQ(P("-2,1").eval(Rational(std::int64_t{7})), Rational(std::int64_t{5}));
    EXPECT_EQ(P("1,0,1").eval(Rational(BigInt(1), BigInt(2))),
              Rational(BigInt(5), BigInt(4)));
}

TEST(UPolyFixed, PythonOracleGcdAndResultant)
{
    for (const Case &c : kCases) {
        const UPoly a = P(c.a), b = P(c.b);
        EXPECT_EQ(S(UPoly::gcd(a, b)), c.g) << c.a << " vs " << c.b;
        EXPECT_EQ(UPoly::resultant(a, b).toString(), c.r) << c.a << " vs " << c.b;
    }
}

TEST(UPolyProperty, RingAndDivisionInvariants)
{
    std::uint64_t state = 0x5A17C0DEF00DBAULL;
    for (int iter = 0; iter < 5000; ++iter) {
        const UPoly a = rndPoly(state, 6);
        const UPoly b = rndPoly(state, 6);
        const UPoly c = rndPoly(state, 6);

        EXPECT_EQ(a + b, b + a);
        EXPECT_EQ(a * b, b * a);
        EXPECT_EQ((a + b) + c, a + (b + c));
        EXPECT_EQ((a * b) * c, a * (b * c));
        EXPECT_EQ(a * (b + c), a * b + a * c);
        EXPECT_EQ((a + b) - b, a);
        EXPECT_EQ(a - a, UPoly());

        if (!b.isZero()) {
            UPoly q, r;
            UPoly::divMod(a, b, q, r);
            ASSERT_EQ(q * b + r, a) << S(a) << " / " << S(b);
            ASSERT_TRUE(r.isZero() || r.deg() < b.deg());
        }
    }
}

TEST(UPolyProperty, GcdInvariants)
{
    std::uint64_t state = 0x1234ABCD5678EF90ULL;
    for (int iter = 0; iter < 3000; ++iter) {
        const UPoly u = rndPoly(state, 3);
        const UPoly v = rndPoly(state, 3);
        const UPoly g0 = rndPoly(state, 2);
        if (g0.isZero())
            continue;
        const UPoly a = g0 * u;
        const UPoly b = g0 * v;
        if (a.isZero() || b.isZero())
            continue;
        const UPoly g = UPoly::gcd(a, b);

        ASSERT_EQ(g.lc(), Rational(std::int64_t{1})); // monic
        UPoly q, r;
        UPoly::divMod(a, g, q, r);
        ASSERT_TRUE(r.isZero()) << S(a) << " gcd " << S(b) << " = " << S(g);
        UPoly::divMod(b, g, q, r);
        ASSERT_TRUE(r.isZero());
        // gcd is associative and commutative up to monicity.
        ASSERT_EQ(UPoly::gcd(a, UPoly::gcd(b, a)), g);
    }
}

TEST(UPolyProperty, Squarefree)
{
    std::uint64_t state = 0xC0FFEE1234567890ULL;
    for (int iter = 0; iter < 3000; ++iter) {
        // Build a product of pairwise-coprime squarefree factors with
        // powers: a = f1^3 * f2 * f3^2. Random polys are neither coprime
        // nor squarefree, so reduce both properties explicitly.
        UPoly f1 = rndPoly(state, 2).squarefreePart();
        UPoly f2 = rndPoly(state, 2).squarefreePart();
        UPoly f3 = rndPoly(state, 1).squarefreePart();
        UPoly g = UPoly::gcd(f1, f2);
        if (!g.isConst()) {
            UPoly q, r;
            UPoly::divMod(f2, g, q, r);
            f2 = q;
        }
        g = UPoly::gcd(f1 * f2, f3);
        if (!g.isConst()) {
            UPoly q, r;
            UPoly::divMod(f3, g, q, r);
            f3 = q;
        }
        if (f1.isZero() || f2.isZero() || f3.isZero() || f1.isConst())
            continue;
        const UPoly a = f1 * f1 * f1 * f2 * f3 * f3;

        const UPoly sfp = a.squarefreePart();
        EXPECT_EQ(UPoly::gcd(sfp, sfp.derivative()).isConst(), true);
        // squarefreePart is defined up to a rational scalar: compare
        // cross-multiplied by leading coefficients.
        const UPoly prod = f1 * f2 * f3;
        ASSERT_EQ(sfp * prod.lc(), prod * sfp.lc())
            << S(a) << " sfp=" << S(sfp) << " prod=" << S(prod);

        const std::vector<UPoly> fs = a.squarefreeDecomposition();
        UPoly rebuild = UPoly(Rational(a.lc()));
        for (std::size_t i = 0; i < fs.size(); ++i)
            rebuild = rebuild * fs[i].powUInt(i + 1);
        ASSERT_EQ(rebuild, a) << S(a);
        for (const UPoly &f : fs) {
            if (f.isConst())
                continue;
            ASSERT_EQ(f.lc(), Rational(std::int64_t{1}));
            ASSERT_TRUE(UPoly::gcd(f, f.derivative()).isConst());
        }
    }
}

TEST(UPolyProperty, ResultantIdentities)
{
    std::uint64_t state = 0x9E3779B97F4A7C15ULL;
    for (int iter = 0; iter < 3000; ++iter) {
        const UPoly a = rndPoly(state, 4);
        const UPoly b = rndPoly(state, 3);
        const UPoly c = rndPoly(state, 3);
        if (a.isZero() || b.isZero() || c.isZero())
            continue;

        // Sign symmetry.
        const Rational rab = UPoly::resultant(a, b);
        const Rational rba = UPoly::resultant(b, a);
        const long long mn = static_cast<long long>(a.deg()) *
                             static_cast<long long>(b.deg());
        ASSERT_EQ(rab, (mn & 1) ? -rba : rba);

        // Multiplicativity in both arguments.
        ASSERT_EQ(UPoly::resultant(a, b * c), rab * UPoly::resultant(a, c))
            << S(a) << " ; " << S(b) << " ; " << S(c);
        ASSERT_EQ(UPoly::resultant(a * b, c),
                  UPoly::resultant(a, c) * UPoly::resultant(b, c));

        // Evaluation oracle: res(A, x - r) == A(r).
        const std::int64_t r = static_cast<std::int64_t>(nextU64(state) % 41) - 20;
        const UPoly lin = UPoly(std::vector<Rational>{Rational(-r),
                                                      Rational(std::int64_t{1})});
        ASSERT_EQ(UPoly::resultant(a, lin), a.eval(Rational(r)))
            << S(a) << " at " << r;
    }
}
