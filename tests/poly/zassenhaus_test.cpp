#include <numkit/cas/poly/zassenhaus.hpp>

#include <gtest/gtest.h>

namespace {

using numkit::cas::BigInt;
using numkit::cas::Rational;
using numkit::cas::UPoly;

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

std::vector<BigInt> IB(const std::vector<std::int64_t> &cs)
{
    std::vector<BigInt> out;
    for (std::int64_t c : cs)
        out.push_back(BigInt(c));
    return out;
}

std::string S(const std::vector<BigInt> &p)
{
    std::string out;
    for (const BigInt &c : p) {
        if (!out.empty())
            out += " ";
        out += c.toString();
    }
    return out;
}

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

// product reconstruction (the integer factors multiply back to the
// primitive part, positive leading coefficient).
void verifyReconstruction(const std::vector<BigInt> &f,
                           const std::vector<std::vector<BigInt>> &factors)
{
    ASSERT_FALSE(factors.empty());
    std::vector<BigInt> prod{BigInt(1)};
    for (const auto &g : factors) {
        ASSERT_GE(g.size(), 2u) << "constant/degenerate factor";
        ASSERT_FALSE(g.back().isNegative());
        prod = [&] {
            std::vector<BigInt> out = prod;
            // small multiplication directly
            std::vector<BigInt> r(out.size() + g.size() - 1, BigInt(0));
            for (std::size_t i = 0; i < out.size(); ++i)
                for (std::size_t j = 0; j < g.size(); ++j)
                    r[i + j] = r[i + j] + out[i] * g[j];
            while (!r.empty() && r.back().isZero())
                r.pop_back();
            return r;
        }();
    }
    // f normalized to its primitive part (content stripped)
    std::vector<BigInt> fn = f;
    if (fn.back().isNegative())
        for (BigInt &c : fn)
            c = -c;
    BigInt cont(0);
    for (const BigInt &c : fn)
        if (!c.isZero())
            cont = BigInt::gcd(cont, c);
    if (!cont.isZero() && !(cont == BigInt(1))) {
        for (BigInt &c : fn) {
            BigInt q, r;
            BigInt::divMod(c, cont, q, r);
            fn = fn; // placeholder
        }
        std::vector<BigInt> red;
        for (const BigInt &c : fn) {
            BigInt q, r;
            BigInt::divMod(c, cont, q, r);
            red.push_back(q);
        }
        fn = red;
    }
    while (!fn.empty() && fn.back().isZero())
        fn.pop_back();
    ASSERT_EQ(S(prod), S(fn));
}

} // namespace

TEST(ZassenhausFixed, Classics)
{
    // x^2 - 1 = (x-1)(x+1)
    verifyReconstruction(IB({-1, 0, 1}), numkit::cas::factorPrimitiveInteger(IB({-1, 0, 1})));
    EXPECT_EQ(numkit::cas::factorPrimitiveInteger(IB({-1, 0, 1})).size(), 2u);

    // x^4 - 5x^2 + 6 = (x^2-2)(x^2-3)
    const auto f2 = numkit::cas::factorPrimitiveInteger(IB({6, 0, -5, 0, 1}));
    ASSERT_EQ(f2.size(), 2u);
    verifyReconstruction(IB({6, 0, -5, 0, 1}), f2);

    // x^2 + 1 irreducible
    EXPECT_EQ(numkit::cas::factorPrimitiveInteger(IB({1, 0, 1})).size(), 1u);
    // x^3 - 2 irreducible (no rational root)
    EXPECT_EQ(numkit::cas::factorPrimitiveInteger(IB({-2, 0, 0, 1})).size(), 1u);
    // (x^3-2)(x+1) = x^4 + x^3 - 2x - 2
    const auto f3 = numkit::cas::factorPrimitiveInteger(IB({-2, -2, 0, 1, 1}));
    ASSERT_EQ(f3.size(), 2u);
    verifyReconstruction(IB({-2, -2, 0, 1, 1}), f3);
    // linear input returns itself
    EXPECT_EQ(numkit::cas::factorPrimitiveInteger(IB({3, 7})).size(), 1u);
}

// Guard for bugs/opened/poly/zassenhaus-cubic-cofactor-unsplit.md:
// the cubic cofactor must split into (x-10/3)(x^2+8/3x+8/3).
TEST(ZassenhausFixed, QuarticCubicSplit) // guard for the closed bug
{
    const UPoly f = P("320,-16,-144,-54,27");
    const auto fs = numkit::cas::factorOverQ(f);
    ASSERT_EQ(fs.size(), 3u);
}

// Constant-term sieve edges: factors with a ZERO constant term make
// the sieve inapplicable (F(0) = 0 divides nothing) and it must turn
// itself off; the reconstruction still has to split the polynomial.
TEST(ZassenhausFixed, ZeroConstantTermFactors)
{
    // x*(x+2)*(x-3) = x^3 - x^2 - 6x
    const auto f = numkit::cas::factorPrimitiveInteger(IB({0, -6, -1, 1}));
    ASSERT_EQ(f.size(), 3u);
    verifyReconstruction(IB({0, -6, -1, 1}), f);

    // (2x)*(3x^2+5) = 6x^3 + 10x: non-monic with a zero const term.
    const auto g = numkit::cas::factorPrimitiveInteger(IB({0, 10, 0, 6}));
    ASSERT_EQ(g.size(), 2u);
    verifyReconstruction(IB({0, 10, 0, 6}), g);
}

TEST(ZassenhausFixed, RationalFactorization)
{
    // Monic rational input.
    const std::vector<UPoly> f = numkit::cas::factorOverQ(P("-2,0,1"));
    ASSERT_EQ(f.size(), 1u); // x^2 - 2 irreducible over Q

    const std::vector<UPoly> g = numkit::cas::factorOverQ(P("6,0,-5,0,1"));
    ASSERT_EQ(g.size(), 2u);
    UPoly prod(Rational(std::int64_t{1}));
    for (const UPoly &q : g)
        prod = prod * q;
    EXPECT_EQ(prod, P("6,0,-5,0,1").squarefreePart()); // monic factors multiply to the monic associate

    // Non-monic rational input: 2x^2 - 8 = 2(x-2)(x+2); factors monic.
    const std::vector<UPoly> h = numkit::cas::factorOverQ(P("-8,0,2"));
    ASSERT_EQ(h.size(), 2u);
    EXPECT_EQ(h[0], P("-2,1"));
    EXPECT_EQ(h[1], P("2,1"));
}

// Disabled pending bugs/opened/poly/zassenhaus-cubic-cofactor-unsplit.md:
// random assemblies hit the unsplit-cofactor shape.
TEST(ZassenhausProperty, AssembleFromKnownFactors)
{
    std::uint64_t state = 0x2A5E11F00DCAULL;
    int done = 0;
    while (done < 60) {
        // Plant linears and quadratics (possibly sharing factors and
        // duplicates); factorOverQ must return the monic irreducibles
        // with correct multiplicities.
        const int k = 2 + static_cast<int>(nextU64(state) % 2);
        std::vector<std::vector<std::int64_t>> parts;
        for (int i = 0; i < k; ++i) {
            const std::int64_t a = 1 + static_cast<std::int64_t>(nextU64(state) % 4);
            const std::int64_t b = static_cast<std::int64_t>(nextU64(state) % 21) - 10;
            parts.push_back(nextU64(state) % 2 == 0
                                ? std::vector<std::int64_t>{b, a}
                                : std::vector<std::int64_t>{b, b, a});
        }
        std::vector<Rational> fcs{Rational(std::int64_t{1})};
        for (const auto &part : parts) {
            std::vector<Rational> pcs;
            for (std::int64_t c : part)
                pcs.push_back(Rational(c));
            const UPoly pp(pcs);
            std::vector<Rational> rcs(fcs.size() + pcs.size() - 1, Rational(std::int64_t{0}));
            for (std::size_t i = 0; i < fcs.size(); ++i)
                for (std::size_t j = 0; j < pcs.size(); ++j)
                    rcs[i + j] = rcs[i + j] + fcs[i] * pcs[j];
            while (rcs.size() > 1 && rcs.back().isZero())
                rcs.pop_back();
            fcs = rcs;
        }
        const UPoly f(fcs);
        if (f.isZero() || f.deg() < 1)
            continue;

        const std::vector<UPoly> factors = numkit::cas::factorOverQ(f);
        ASSERT_FALSE(factors.empty());

        // product reconstructs the monic associate of f
        UPoly prod(Rational(std::int64_t{1}));
        for (const UPoly &g : factors)
            prod = prod * g;
        ASSERT_EQ(prod * f.lc(), f) << "reconstruction broken";

        // every IRREDUCIBLE planted factor (monic associate) divides f
        // and appears with at least the planted multiplicity; reducible
        // parts (e.g. x^2) are legitimately split further by the
        // factorization and are not asserted verbatim.
        for (const auto &part : parts) {
            std::vector<Rational> pcs;
            for (std::int64_t c : part)
                pcs.push_back(Rational(c));
            const UPoly pf(pcs);
            {
                // skip parts with a rational root (reducible)
                bool hasRoot = false;
                for (std::int64_t r = -40; r <= 40; ++r) {
                    if (pf.eval(Rational(r)).isZero()) {
                        hasRoot = true;
                        break;
                    }
                }
                if (hasRoot)
                    continue;
            }
            UPoly q, r;
            UPoly::divMod(pf, UPoly(pf.lc()), q, r); // monic associate
            UPoly monic = q;
            UPoly::divMod(f, monic, q, r);
            ASSERT_TRUE(r.isZero()) << "planted factor does not divide f";
            std::size_t planted = 0;
            for (const auto &other : parts) {
                std::vector<Rational> ocs;
                for (std::int64_t c : other)
                    ocs.push_back(Rational(c));
                const UPoly of_(ocs);
                UPoly oq, orr;
                UPoly::divMod(of_, UPoly(of_.lc()), oq, orr);
                if (oq == monic)
                    ++planted;
            }
            std::size_t got = 0;
            for (const UPoly &g : factors)
                if (g == monic)
                    ++got;
            ASSERT_GE(got, planted) << "planted factor multiplicity lost";
        }
        ++done;
    }
}

TEST(ZassenhausProperty, RandomPolynomialsReconstruct)
{
    std::uint64_t state = 0x99AABBCCDDEE00ULL;
    for (int iter = 0; iter < 200; ++iter) {
        const int deg = 2 + static_cast<int>(nextU64(state) % 6);
        std::vector<BigInt> f;
        for (int i = 0; i < deg; ++i)
            f.push_back(BigInt(static_cast<std::int64_t>(nextU64(state) % 41) - 20));
        f.push_back(BigInt(1 + static_cast<std::int64_t>(nextU64(state) % 4)));
        if (f.front().isZero())
            f[0] = BigInt(1);
verifyReconstruction(f, numkit::cas::factorPrimitiveInteger(f));
        // Determinism.
        const auto f1 = numkit::cas::factorPrimitiveInteger(f);
        const auto f2 = numkit::cas::factorPrimitiveInteger(f);
        ASSERT_EQ(f1.size(), f2.size());
        for (std::size_t i = 0; i < f1.size(); ++i)
            ASSERT_EQ(S(f1[i]), S(f2[i]));
    }
}
