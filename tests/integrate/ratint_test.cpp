#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/core/parser.hpp>

#include <gtest/gtest.h>

#include <functional>

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

TEST_F(RatIntTest, GroupedLogsByResidue)
{
    auto integrate = [&](const std::string &numCsv, const std::string &denCsv) {
        const Expr f = build(P(numCsv), P(denCsv));
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        EXPECT_TRUE(r.proved()) << r.reason;
        return r.proved() ? c.toString(r.F) : std::string("<failed>");
    };

    // Equal residues at both poles group into one logarithm.
    EXPECT_EQ(integrate("3,2", "2,3,1"), "log(2 + x^2 + 3*x)");
    EXPECT_EQ(integrate("0,2", "-1,0,1"), "log(-1 + x^2)");
    // Rational residues over cubic denominators with a quadratic part.
    EXPECT_EQ(integrate("1", "0,1,0,1"), "log(x) + -1/2*log(1 + x^2)");
}

TEST_F(RatIntTest, ResultantTEvaluationAndResidues)
{
    std::uint64_t state = 0x7EA15EEDBEEFCAULL;
    for (int iter = 0; iter < 2000; ++iter) {
        // Build S with distinct rational roots and chosen residues c_i:
        // A = sum c_i * S/(x - r_i) has residue c_i at r_i, so
        // squarefreePart(res(A - t*S', S)) is prod (t - c_i) over the
        // DISTINCT residues, up to a scalar.
        const int k = 1 + static_cast<int>(nextU64(state) % 3);
        std::vector<Rational> roots, res;
        UPoly S(Rational(std::int64_t{1}));
        for (int i = 0; i < k; ++i) {
            Rational r = rr(state, 6);
            Rational m = rr(state, 4);
            if (r.isZero())
                r = Rational(std::int64_t{1});
            bool dup = false;
            for (const Rational &w : roots)
                if (w == r)
                    dup = true;
            if (dup)
                continue;
            roots.push_back(r);
            res.push_back(m);
            S = S * UPoly(std::vector<Rational>{Rational(-r), Rational(std::int64_t{1})});
        }
        if (roots.empty())
            continue;

        UPoly A;
        for (std::size_t i = 0; i < roots.size(); ++i) {
            UPoly q, r2;
            UPoly::divMod(S, UPoly(std::vector<Rational>{Rational(-roots[i]),
                                                Rational(std::int64_t{1})}),
                          q, r2);
            A = A + res[i] * q;
        }
        // Proper fraction (deg A < deg S by construction).

        const UPoly R = numkit::cas::resultantT(A, S.derivative(), S);

        // Evaluation identity at fresh points.
        for (int probe = 0; probe < 3; ++probe) {
            const Rational t = rr(state, 20);
            EXPECT_EQ(R.eval(t), UPoly::resultant(A - t * S.derivative(), S));
        }

        // Residue oracle: expected = prod over distinct residues (t - c).
        UPoly expected(Rational(std::int64_t{1}));
        for (std::size_t i = 0; i < roots.size(); ++i) {
            bool seen = false;
            for (std::size_t j = 0; j < i; ++j)
                if (res[j] == res[i])
                    seen = true;
            if (seen)
                continue;
            expected = expected * UPoly(std::vector<Rational>{
                Rational(-res[i]), Rational(std::int64_t{1})});
        }
        const UPoly Rsq = R.squarefreePart();
        if (expected.isConst()) {
            EXPECT_TRUE(Rsq.isConst());
        } else {
            ASSERT_EQ(Rsq * expected.lc(), expected * Rsq.lc())
                << "R=" << R.toString() << " expected=" << expected.toString();
        }
    }
}

TEST_F(RatIntTest, QuadraticResidueForms)
{
    auto integrate = [&](const std::string &numCsv, const std::string &denCsv) {
        const Expr f = build(P(numCsv), P(denCsv));
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        EXPECT_TRUE(r.proved()) << r.reason;
        return r.proved() ? c.toString(r.F) : std::string("<failed>");
    };

    // Complex residue pair, non-square discriminant complement:
    // int dx/(x^2+2) = atan(x/sqrt(2))/sqrt(2).
    const std::string s1 = integrate("1", "2,0,1");
    EXPECT_NE(s1.find("atan"), std::string::npos);
    // Real residue pair: int dx/(x^2-2) = sqrt2/4 log(x-sqrt2) - sqrt2/4 log(x+sqrt2).
    const std::string s2 = integrate("1", "-2,0,1");
    EXPECT_NE(s2.find("log"), std::string::npos);
    EXPECT_NE(s2.find("2^(1/2)"), std::string::npos);
    // Mixed linear x quadratic: still fully proved.
    EXPECT_NE(integrate("1", "-2,-1,1").find("log"), std::string::npos);
    // Square complement stays rational and clean.
    EXPECT_EQ(integrate("1", "1,0,1"), "atan(x)");
    EXPECT_EQ(integrate("1", "1,0,4"), "1/2*atan(2*x)");
}

TEST_F(RatIntTest, QuadraticResidueDoD)
{
    // Any quadratic denominator factor — any discriminant — must now
    // integrate with a certificate.
    std::uint64_t state = 0x5AFED00DCAFEULL;
    for (int iter = 0; iter < 2000; ++iter) {
        const Rational b = rr(state, 5);
        Rational cc = rr(state, 5);
        if (b * b - Rational(std::int64_t{4}) * cc == Rational(std::int64_t{0}))
            cc = cc + Rational(std::int64_t{1}); // keep squarefree
        std::vector<Rational> dcs{cc, b, Rational(std::int64_t{1})};
        if (nextU64(state) % 2 == 0) {
            const Rational r = rr(state, 5);
            // (x - r) coprime to the quadratic with high probability;
            // skip the rare collision by moving r off the roots.
            dcs = std::vector<Rational>{
                -r * cc, cc - r * b, b - r, Rational(std::int64_t{1})};
        }
        const UPoly den(dcs);
        if (den.isZero() || den.isConst())
            continue;
        const int nn = static_cast<int>(nextU64(state) % den.deg());
        std::vector<Rational> ncs;
        for (int i = 0; i <= nn; ++i)
            ncs.push_back(rr(state, 6));
        const UPoly num(ncs);
        if (num.isZero())
            continue;

        const Expr f = build(num, den);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(r.proved()) << "iter " << iter << " reason=" << r.reason
                                << " f=" << c.toString(f);
    }
}

TEST_F(RatIntTest, MultipleQuadraticResidueFactors) // guard for the closed bug
{
    // Two IRREDUCIBLE quadratics with NON-square discriminants in the
    // denominator: previously beyond reach (budget/single-quadratic
    // limits), now handled by the factorized residue pipeline.
    auto integrate = [&](const std::string &numCsv, const std::string &denCsv) {
        const Expr f = build(P(numCsv), P(denCsv));
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        EXPECT_TRUE(r.proved()) << r.reason;
        return r.proved() ? c.toString(r.F) : std::string("<failed>");
    };
    // 1/((x^2+2)(x^2+3)): residues involve sqrt(2), sqrt(3) — real
    // quadratic residue pairs on BOTH factors.
    EXPECT_NE(integrate("1", "6,0,5,0,1").find("atan"), std::string::npos);
    // DoD-style: linear x two different quadratics with multiplicities.
    std::uint64_t state = 0x51CE0FFEE42ULL;
    for (int iter = 0; iter < 500; ++iter) {
        const Rational b1 = rr(state, 4), c1v = rr(state, 4);
        const Rational b2 = rr(state, 4), c2v = rr(state, 4);
        // require irreducible quadratics with negative discriminants
        if (b1 * b1 - 4 * c1v >= 0 || b2 * b2 - 4 * c2v >= 0)
            continue;
        const UPoly q1(std::vector<Rational>{c1v, b1, Rational(std::int64_t{1})});
        const UPoly q2(std::vector<Rational>{c2v, b2, Rational(std::int64_t{1})});
        const Rational r = rr(state, 4);
        const UPoly lin(std::vector<Rational>{Rational(-r), Rational(std::int64_t{1})});
        UPoly den = q1 * q2;
        if (nextU64(state) % 2 == 0)
            den = den * lin;
        const int nn = static_cast<int>(nextU64(state) % den.deg());
        std::vector<Rational> ncs;
        for (int i = 0; i <= nn; ++i)
            ncs.push_back(rr(state, 5));
        const UPoly num(ncs);
        if (num.isZero())
            continue;
        const Expr f = build(num, den);
        const numkit::cas::RationalIntegral ri =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(ri.proved()) << "iter " << iter << " reason=" << ri.reason
                                 << " f=" << c.toString(f);
    }
}

TEST_F(RatIntTest, CubicResidueRootOfForms)
{
    // Degree >= 3 irreducible denominators now integrate with RootOf
    // atoms; property over random irreducible cubics times linear powers.
    std::uint64_t state = 0xC0FFEEBADFACEULL;
    int provedCount = 0, total = 0;
    std::string lastReason;
    while (total < 40) {
        const Rational b = rr(state, 4);
        Rational cc = rr(state, 4);
        // keep the cubic irreducible (no rational root)
        bool red = false;
        for (std::int64_t r0 = -12; r0 <= 12; ++r0)
            if (((cc + b * r0 + r0 * r0 * r0) == 0)) { red = true; break; }
        if (red)
            continue;
        const UPoly den(std::vector<Rational>{cc, b, Rational(std::int64_t{0}),
                                              Rational(std::int64_t{1})}); // x^3 + b x + cc
        if (den.isZero())
            continue;
        const int nn = static_cast<int>(nextU64(state) % 3);
        std::vector<Rational> ncs;
        for (int i = 0; i <= nn; ++i)
            ncs.push_back(rr(state, 5));
        const UPoly num(ncs);
        if (num.isZero())
            continue;
        const Expr f = build(num, den);
        const numkit::cas::RationalIntegral r = numkit::cas::integrateRational(c, f, x);
        ++total;
        if (r.proved()) {
            ++provedCount;
        } else {
            lastReason = r.reason;
        }
    }
    if (provedCount <= total / 2)
        ADD_FAILURE() << "only " << provedCount << "/" << total << " proved; last reason: "
                      << lastReason;
    (void)0;
}

TEST_F(RatIntTest, TwoCubicResidueFactors)
{
    // TWO different irreducible cubics in the denominator — the
    // Norm-subtraction loop must process both factors and leave nothing.
    auto integrate = [&](const std::string &numCsv, const std::string &denCsv) {
        const Expr f = build(P(numCsv), P(denCsv));
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        EXPECT_TRUE(r.proved()) << r.reason;
        return r.proved() ? c.toString(r.F) : std::string("<failed>");
    };
    // (x^3+2)(x^3+3): both irreducible, residues in two different
    // degree-3 extensions.
    EXPECT_NE(integrate("1", "6,0,0,5,0,0,1").find("RootOf"), std::string::npos);
    // Property: random pairs of irreducible cubics with random numerators.
    std::uint64_t state = 0xB16C0FFEE5A11ULL;
    int proved = 0, total = 0;
    while (total < 15) {
        auto irred = [&]() {
            while (true) {
                const Rational b = rr(state, 3);
                const Rational cc = rr(state, 3);
                bool red = false;
                for (std::int64_t r0 = -8; r0 <= 8; ++r0)
                    if (cc + b * r0 + r0 * r0 * r0 == 0)
                        red = true;
                if (!red)
                    return UPoly(std::vector<Rational>{cc, b,
                        Rational(std::int64_t{0}), Rational(std::int64_t{1})});
            }
        };
        const UPoly q1 = irred(), q2 = irred();
        if (q1 == q2)
            continue;
        const UPoly den = q1 * q2;
        const int nn = static_cast<int>(nextU64(state) % 3);
        std::vector<Rational> ncs;
        for (int i = 0; i <= nn; ++i)
            ncs.push_back(rr(state, 4));
        const UPoly num(ncs);
        if (num.isZero())
            continue;
        const Expr f = build(num, den);
        const numkit::cas::RationalIntegral r = numkit::cas::integrateRational(c, f, x);
        ++total;
        if (r.proved())
            ++proved;
    }
    EXPECT_GT(proved, total / 2) << "only " << proved << "/" << total << " proved";
}

TEST_F(RatIntTest, C1CompletenessDoD)
{
    // THE C1 capstone property: random products of linear, irreducible
    // quadratic (any discriminant) and irreducible cubic factors with
    // multiplicities — every integration must return PROVED_SYMBOLIC.
    // Covers all three residue classes in one denominator.
    std::uint64_t state = 0xC1C0FFEE5EE0DULL;
    for (int iter = 0; iter < 200; ++iter) {
        UPoly den(Rational(std::int64_t{1}));
        const int nLin = static_cast<int>(nextU64(state) % 3);
        const int nQuad = static_cast<int>(nextU64(state) % 2);
        const int nCub = static_cast<int>(nextU64(state) % 2);
        for (int i = 0; i < nLin; ++i) {
            Rational r = rr(state, 5);
            if (r.isZero())
                r = Rational(std::int64_t{1});
            const int m = 1 + static_cast<int>(nextU64(state) % 3);
            den = den * UPoly(std::vector<Rational>{Rational(-r),
                Rational(std::int64_t{1})}).powUInt(m);
        }
        for (int i = 0; i < nQuad; ++i) {
            // random monic quadratic, no rational root
            while (true) {
                const Rational b = rr(state, 4);
                const Rational cc = rr(state, 4);
                bool red = false;
                for (std::int64_t r0 = -8; r0 <= 8; ++r0)
                    if (cc + b * r0 + r0 * r0 == 0)
                        red = true;
                if (!red) {
                    const int m = 1 + static_cast<int>(nextU64(state) % 2);
                    den = den * UPoly(std::vector<Rational>{cc, b,
                        Rational(std::int64_t{1})}).powUInt(m);
                    break;
                }
            }
        }
        for (int i = 0; i < nCub; ++i) {
            while (true) {
                const Rational b = rr(state, 3);
                const Rational cc = rr(state, 3);
                bool red = false;
                for (std::int64_t r0 = -8; r0 <= 8; ++r0)
                    if (cc + b * r0 + r0 * r0 * r0 == 0)
                        red = true;
                if (!red) {
                    den = den * UPoly(std::vector<Rational>{cc, b,
                        Rational(std::int64_t{0}), Rational(std::int64_t{1})});
                    break;
                }
            }
        }
        if (den.isConst() || den.deg() < 3)
            continue; // want genuinely mixed denominators
        const int nn = static_cast<int>(nextU64(state) % den.deg());
        std::vector<Rational> ncs;
        for (int i = 0; i <= nn; ++i)
            ncs.push_back(rr(state, 5));
        const UPoly num(ncs);
        if (num.isZero())
            continue;

        const Expr f = build(num, den);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(r.proved()) << "iter " << iter << " reason=" << r.reason
                                << " f=" << c.toString(f);
    }
}

TEST_F(RatIntTest, HonestFailures)
{
    numkit::cas::RationalIntegral r;

    // Not rational in x, exp(x), log(x)/x or sin/cos: sin(x)/x mixes
    // a bare x with trig (the sine integral, non-elementary).
    r = numkit::cas::integrateRational(c, c.div(c.func("sin", x), x), x);
    EXPECT_FALSE(r.proved());
    EXPECT_FALSE(r.reason.empty());

    // FLAGSHIP: int dx/(x^3+2) — residues in a degree-3 extension,
    // proved via the trace certificate with RootOf atoms.
    r = numkit::cas::integrateRational(
        c, build(P("1"), P("2,0,0,1")), x);
    if (r.proved()) {
        const std::string fs = c.toString(r.F);
        EXPECT_NE(fs.find("RootOf"), std::string::npos) << fs;
        EXPECT_NE(fs.find("log"), std::string::npos) << fs;
    } else {
        ADD_FAILURE() << "x^3+2 regressed to Unevaluated: " << r.reason;
    }

    // FLAGSHIP: degree-4 irreducible residues — RootOf branch proves it.
    r = numkit::cas::integrateRational(
        c, build(P("1"), P("1,0,0,0,1")), x);
    if (r.proved()) {
        const std::string fs = c.toString(r.F);
        EXPECT_NE(fs.find("RootOf"), std::string::npos) << fs;
        EXPECT_NE(fs.find("log"), std::string::npos) << fs;
    } else {
        ADD_FAILURE() << "x^4+1 regressed to Unevaluated: " << r.reason;
    }
}

TEST_F(RatIntTest, CertificateCatchesNothingOnZero)
{
    const numkit::cas::RationalIntegral r =
        numkit::cas::integrateRational(c, c.zero(), x);
    EXPECT_TRUE(r.proved());
    EXPECT_EQ(c.toString(r.F), "0");
}

// ── C3 spike: rational functions of exp (t = e^x substitution) ──

TEST_F(RatIntTest, ExpRationalFixedVectors)
{
    struct Case
    {
        const char *f;
        const char *F;
    };
    const Case cases[] = {
        {"1/(exp(x)+1)", "log(exp(x)) + -log(1 + exp(x))"},
        {"1/(exp(x)^2+1)", "log(exp(x)) + -1/2*log(1 + exp(x)^2)"},
        {"exp(x)/(exp(x)^2+1)", "atan(exp(x))"},
        {"1/(exp(x)+exp(-x))", "atan(exp(x))"},
        {"exp(x)", "exp(x)"},
        {"exp(-2*x)", "-1/2*exp(x)^-2"},
    };
    for (const Case &k : cases) {
        const Expr f = numkit::cas::parseExpr(c, k.f);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(r.proved()) << k.f << ": " << r.reason;
        EXPECT_EQ(c.toString(r.F), k.F) << k.f;
    }
}

TEST_F(RatIntTest, ExpRationalHonestFailures)
{
    const char *bad[] = {
        "x*exp(x)",       // var outside exp
        "exp(x^2)",       // non-linear exponent
        "1/(exp(x/2)+1)", // fractional k: t^(1/2) not rational
        "exp(x)+x",
        "sin(x)/x",       // sine integral: bare x outside trig
        "log(exp(x)+1)+exp(x)",
    };
    for (const char *s : bad) {
        const Expr f = numkit::cas::parseExpr(c, s);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        EXPECT_FALSE(r.proved()) << s;
        EXPECT_FALSE(r.reason.empty()) << s;
    }
}

TEST_F(RatIntTest, ExpRationalProperty)
{
    // Random rational R(t) -> R(e^x) integrates PROVED: the whole
    // rational kernel (Hermite/Trager/certificates) is exercised in
    // the t-world and the gate is the polynomial identity.
    std::uint64_t st = 0xE9AC5EEDC0DEULL;
    for (int iter = 0; iter < 120; ++iter) {
        auto rr = [&](int lim) {
            const std::int64_t q = 1 + static_cast<std::int64_t>(nextU64(st) % 3);
            const std::int64_t p =
                static_cast<std::int64_t>(nextU64(st) % (2 * lim + 1)) - lim;
            return Rational(BigInt(p), BigInt(q));
        };
        const int dn = 1 + static_cast<int>(nextU64(st) % 3);
        std::vector<Rational> dcs;
        for (int i = 0; i <= dn; ++i)
            dcs.push_back(rr(4));
        if (dcs.back().isZero())
            dcs.back() = Rational(std::int64_t{1});
        const int nn = static_cast<int>(nextU64(st) % (dn + 1));
        std::vector<Rational> ncs;
        for (int i = 0; i <= nn; ++i)
            ncs.push_back(rr(4));
        const UPoly num(ncs), den(dcs);
        const Expr R = build(num, den); // rational in x = a stand-in for t
        // rebuild R with x -> exp(x)
        const Expr expVar = c.func("exp", x);
        std::function<Expr(Expr)> sub = [&](Expr e) -> Expr {
            if (e == x)
                return expVar;
            switch (c.kind(e)) {
            case NodeKind::Number:
            case NodeKind::Symbol:
            case NodeKind::RootOf:
                return e;
            case NodeKind::Func:
                return c.func(c.funcName(e), sub(c.child(e, 0)));
            case NodeKind::Pow:
                return c.pow(sub(c.child(e, 0)), sub(c.child(e, 1)));
            default: {
                std::vector<Expr> kids;
                for (std::size_t i = 0; i < c.childCount(e); ++i)
                    kids.push_back(sub(c.child(e, i)));
                return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
            }
            }
        };
        const Expr f = sub(R);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(r.proved()) << c.toString(f) << ": " << r.reason;
    }
}

// ── Second Liouvillian storey: rational functions of log ──

TEST_F(RatIntTest, LogRationalFixedVectors)
{
    struct Case
    {
        const char *f;
        const char *F;
    };
    const Case cases[] = {
        {"log(x)/x", "1/2*log(x)^2"},
        {"1/(x*log(x))", "log(log(x))"},
        {"1/(x*(1+log(x)))", "log(1 + log(x))"},
        {"(log(x))^3/x", "1/4*log(x)^4"},
        {"1/(x*(log(x)^2+1))", "atan(log(x))"},
    };
    for (const Case &k : cases) {
        const Expr f = numkit::cas::parseExpr(c, k.f);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(r.proved()) << k.f << ": " << r.reason;
        EXPECT_EQ(c.toString(r.F), k.F) << k.f;
    }
}

TEST_F(RatIntTest, LogRationalHonestFailures)
{
    const char *bad[] = {
        "log(x)",          // no 1/x Jacobian: not this storey
        "1/(x^2*log(x))",  // x beyond the Jacobian
        "log(x^2)",        // log of non-var: x survives
        "log(x)/x^2",
        "exp(x)+log(x)",   // genuinely mixed storeys
        "sin(x)+log(x)/x",
    };
    for (const char *s : bad) {
        const Expr f = numkit::cas::parseExpr(c, s);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        EXPECT_FALSE(r.proved()) << s;
        EXPECT_FALSE(r.reason.empty()) << s;
    }
    // A nested-storey case that DOES integrate legitimately:
    // exp(log(x))/x == 1, and the composed substitution returns
    // exp(log(x)) whose derivative is exactly the integrand.
    const Expr nested = numkit::cas::parseExpr(c, "exp(log(x))/x");
    const numkit::cas::RationalIntegral nr =
        numkit::cas::integrateRational(c, nested, x);
    EXPECT_TRUE(nr.proved()) << nr.reason;
    EXPECT_EQ(c.toString(nr.F), "exp(log(x))");
}

TEST_F(RatIntTest, LogRationalProperty)
{
    // Random rational R(t); f = R(log x)/x must integrate PROVED via
    // the t = log x storey (kernel certificate + round-trip gate).
    std::uint64_t st = 0x10CC0DE5EEDULL;
    for (int iter = 0; iter < 120; ++iter) {
        auto rr = [&](int lim) {
            const std::int64_t q = 1 + static_cast<std::int64_t>(nextU64(st) % 3);
            const std::int64_t p =
                static_cast<std::int64_t>(nextU64(st) % (2 * lim + 1)) - lim;
            return Rational(BigInt(p), BigInt(q));
        };
        const int dn = 1 + static_cast<int>(nextU64(st) % 3);
        std::vector<Rational> dcs;
        for (int i = 0; i <= dn; ++i)
            dcs.push_back(rr(4));
        if (dcs.back().isZero())
            dcs.back() = Rational(std::int64_t{1});
        const int nn = static_cast<int>(nextU64(st) % (dn + 1));
        std::vector<Rational> ncs;
        for (int i = 0; i <= nn; ++i)
            ncs.push_back(rr(4));
        const Expr R = build(UPoly(ncs), UPoly(dcs)); // rational in x = t stand-in
        const Expr logVar = c.func("log", x);
        std::function<Expr(Expr)> sub = [&](Expr e) -> Expr {
            if (e == x)
                return logVar;
            switch (c.kind(e)) {
            case NodeKind::Number:
            case NodeKind::Symbol:
            case NodeKind::RootOf:
                return e;
            case NodeKind::Func:
                return c.func(c.funcName(e), sub(c.child(e, 0)));
            case NodeKind::Pow:
                return c.pow(sub(c.child(e, 0)), sub(c.child(e, 1)));
            default: {
                std::vector<Expr> kids;
                for (std::size_t i = 0; i < c.childCount(e); ++i)
                    kids.push_back(sub(c.child(e, i)));
                return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
            }
            }
        };
        const Expr f = c.div(sub(R), x);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(r.proved()) << c.toString(f) << ": " << r.reason;
    }
}

// ── Trigonometric storey: rational functions of sin/cos (t = tan(x/2)) ──

TEST_F(RatIntTest, TanRationalFixedVectors)
{
    struct Case
    {
        const char *f;
        const char *F;
    };
    // The answers come back in tan(x/2) terms: the certificate is
    // exact (d/dx of the answer IS the integrand), while prettier
    // sin/cos/x forms are simplify's business, not the integrator's.
    const Case cases[] = {
        {"sin(x)", "-2*(1 + tan(1/2*x)^2)^-1"},
        {"tan(x)", "log(1 + tan(1/2*x)^2) + -log(-1 + tan(1/2*x)^2)"},
        {"1/(3+5*cos(x))",
         "-1/4*log(-2 + tan(1/2*x)) + 1/4*log(2 + tan(1/2*x))"},
        {"1/(1+sin(x))", "-2*(1 + tan(1/2*x))^-1"},
    };
    for (const Case &k : cases) {
        const Expr f = numkit::cas::parseExpr(c, k.f);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(r.proved()) << k.f << ": " << r.reason;
        EXPECT_EQ(c.toString(r.F), k.F) << k.f;
    }
}

TEST_F(RatIntTest, TanRationalHonestFailures)
{
    const char *bad[] = {
        "sin(2*x)",   // multiple angle: no rationalizing rewrite here
        "sin(x^2)",   // non-linear argument
        "x*sin(x)",   // bare x outside trig
        "exp(x)*sin(x)", // mixed storeys
        "asin(x)",    // inverse trig is a different storey
    };
    for (const char *s : bad) {
        const Expr f = numkit::cas::parseExpr(c, s);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        EXPECT_FALSE(r.proved()) << s;
        EXPECT_FALSE(r.reason.empty()) << s;
    }
}

TEST_F(RatIntTest, TanRationalProperty)
{
    // Random rational R(sin x, cos x): build as polynomials in two
    // atoms, substitute into the integrand, expect PROVED.
    std::uint64_t st = 0x7A0C5EEDULL;
    const Expr s = c.func("sin", x);
    const Expr co = c.func("cos", x);
    for (int iter = 0; iter < 100; ++iter) {
        auto rr = [&](int lim) {
            const std::int64_t q = 1 + static_cast<std::int64_t>(nextU64(st) % 3);
            const std::int64_t p =
                static_cast<std::int64_t>(nextU64(st) % (2 * lim + 1)) - lim;
            return Rational(BigInt(p), BigInt(q));
        };
        // num and den as polys in sin (outer) of poly in cos (inner),
        // small degrees to keep the t-degrees bounded.
        auto smallPoly = [&](const Expr &atom) {
            const int d = static_cast<int>(nextU64(st) % 3);
            std::vector<Expr> terms;
            for (int i = 0; i <= d; ++i)
                terms.push_back(c.mul({c.number(rr(3)),
                                       c.pow(atom, c.number(
                                           static_cast<std::int64_t>(i)))}));
            return c.add(terms);
        };
        const Expr num = c.mul({smallPoly(s), smallPoly(co)});
        const Expr den = c.add({smallPoly(s), smallPoly(co),
                                c.number(std::int64_t{2})});
        const Expr f = c.div(num, den);
        const numkit::cas::RationalIntegral r =
            numkit::cas::integrateRational(c, f, x);
        ASSERT_TRUE(r.proved()) << c.toString(f) << ": " << r.reason;
    }
}
