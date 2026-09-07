// corpus_runner_test.cpp — three layers per AGENTS.md for the §7
// corpus machinery (apps/corpus_runner.cpp compiled directly into
// this binary):
//   1. fixed vectors: line parsing, order statistics, statuses and
//      report arithmetic on a hand-built mini corpus;
//   2. property: random rational tasks built as TEXT through the
//      poly->Expr->string pipeline all come back PROVED (the full
//      parse -> integrate -> certificate path, fixed seed);
//   3. boundary: blank/comment-only corpora, malformed lines, empty
//      fields, division-free edge expressions.
#include "corpus_runner.hpp"

#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/integrate/ratint.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

namespace {

using namespace nkcorpus;

CorpusTask task(const char *id, const char *var, const char *expr)
{
    return CorpusTask{id, var, expr};
}

// ── layer 1: fixed vectors ─────────────────────────────────────

TEST(CorpusLine, ParsesTsvWithSpacesInExpr)
{
    CorpusTask t;
    EXPECT_TRUE(parseCorpusLine("r0001\tx\t1/(x^2 + 2)", t));
    EXPECT_EQ(t.id, "r0001");
    EXPECT_EQ(t.var, "x");
    EXPECT_EQ(t.expr, "1/(x^2 + 2)");
}

TEST(CorpusLine, TrimsFieldsAndKeepsInnerSpaces)
{
    CorpusTask t;
    EXPECT_TRUE(parseCorpusLine("  id7 \t  y \t x + 1 + sin( y ) ", t));
    EXPECT_EQ(t.id, "id7");
    EXPECT_EQ(t.var, "y");
    EXPECT_EQ(t.expr, "x + 1 + sin( y )");
}

TEST(CorpusLine, SkipsCommentsAndBlanks)
{
    CorpusTask t;
    EXPECT_FALSE(parseCorpusLine("", t));
    EXPECT_FALSE(parseCorpusLine("   ", t));
    EXPECT_FALSE(parseCorpusLine("# a comment", t));
    EXPECT_FALSE(parseCorpusLine("   # indented comment", t));
    EXPECT_EQ(lineKind(""), LineKind::Skip);
    EXPECT_EQ(lineKind("# c"), LineKind::Skip);
}

TEST(CorpusLine, RejectsMalformed)
{
    const char *bad[] = {
        "no tabs at all",
        "only\tone tab",
        "a\tb\tc\td",
        "\tx\t1/x",          // empty id
        "id\t\t1/x",         // empty var
        "id\tx\t",           // empty expr
        "id\tx\t   ",        // whitespace-only expr
    };
    for (const char *s : bad) {
        CorpusTask t;
        EXPECT_FALSE(parseCorpusLine(s, t)) << "line: '" << s << "'";
        EXPECT_EQ(lineKind(s), LineKind::Malformed) << "line: '" << s << "'";
    }
}

TEST(CorpusStats, MedianVectors)
{
    EXPECT_EQ(medianOf({}), 0u);
    EXPECT_EQ(medianOf({7}), 7u);
    EXPECT_EQ(medianOf({3, 1, 2}), 2u);
    EXPECT_EQ(medianOf({4, 1, 3, 2}), 3u); // (2+3+1)/2 rounded up
    EXPECT_EQ(medianOf({1, 2, 3, 10}), 3u);
}

TEST(CorpusStats, PercentileNearestRank)
{
    EXPECT_EQ(percentileOf({}, 0.95), 0u);
    EXPECT_EQ(percentileOf({42}, 0.95), 42u);
    EXPECT_EQ(percentileOf({1}, 1.0), 1u);
    std::vector<std::uint64_t> v;
    for (std::uint64_t i = 1; i <= 20; ++i)
        v.push_back(i);
    EXPECT_EQ(percentileOf(v, 0.95), 19u); // ceil(0.95*20)=19th smallest
    EXPECT_EQ(percentileOf(v, 1.0), 20u);
    EXPECT_EQ(percentileOf(v, 0.5), 10u);
    EXPECT_EQ(percentileOf(v, 0.0), 0u); // p out of (0,1] rejected
}

TEST(CorpusTask, StatusesOnFixedInputs)
{
    const TaskOutcome proved = runTask(task("t1", "x", "1/x^2"));
    EXPECT_EQ(proved.status, TaskStatus::Proved);
    EXPECT_GT(proved.answerNodes, 0u);

    const TaskOutcome zero = runTask(task("t2", "x", "0"));
    EXPECT_EQ(zero.status, TaskStatus::Proved);

    const TaskOutcome trans = runTask(task("t3", "x", "sin(x)/x"));
    EXPECT_EQ(trans.status, TaskStatus::Unevaluated);
    EXPECT_FALSE(trans.detail.empty());

    const TaskOutcome otherSym = runTask(task("t4", "x", "1/y"));
    EXPECT_EQ(otherSym.status, TaskStatus::Unevaluated);

    const TaskOutcome bad = runTask(task("t5", "x", "1/(x"));
    EXPECT_EQ(bad.status, TaskStatus::ParseError);
    EXPECT_FALSE(bad.detail.empty());
}

TEST(CorpusReport, CountsAndRates)
{
    std::vector<TaskOutcome> o;
    const CorpusReport rep = runCorpus(
        {task("a", "x", "1/x"), task("b", "x", "sin(x)"),
         task("c", "x", "1/(")},
        &o);
    EXPECT_EQ(rep.total, 3u);
    EXPECT_EQ(rep.proved, 1u);
    EXPECT_EQ(rep.unevaluated, 1u);
    EXPECT_EQ(rep.parseErrors, 1u);
    EXPECT_EQ(rep.malformedLines, 0u);
    EXPECT_DOUBLE_EQ(rep.passRatePct(), 100.0 / 3.0);
    EXPECT_DOUBLE_EQ(rep.verificationRatePct(), 50.0);
    ASSERT_EQ(o.size(), 3u);
    EXPECT_EQ(o[0].id, "a");
    EXPECT_EQ(o[2].status, TaskStatus::ParseError);
}

TEST(CorpusReport, DegenerateRatesAreZeroNotNaN)
{
    const CorpusReport empty = runCorpus({});
    EXPECT_EQ(empty.total, 0u);
    EXPECT_DOUBLE_EQ(empty.passRatePct(), 0.0);
    EXPECT_DOUBLE_EQ(empty.verificationRatePct(), 0.0);
    EXPECT_EQ(empty.medianMicros, 0u);
    // All-parse-error corpus: unmeasurable, not "0% verified".
    const CorpusReport allBad = runCorpus({task("e", "x", "@@")});
    EXPECT_EQ(allBad.parseErrors, 1u);
    EXPECT_DOUBLE_EQ(allBad.verificationRatePct(), 0.0);
}

// ── layer 2: property — text tasks through the whole pipeline ──

std::uint64_t nextU64(std::uint64_t &state)
{
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    return state * 0x2545F4914F6CDD1DULL;
}

TEST(CorpusProperty, RandomRationalTextAllProved)
{
    // Same shape as the C1 capstone: products of linear^m, irreducible
    // quadratics and cubics; the task text is the PRINTED form of the
    // fraction, so this exercises parse -> toRational -> Hermite ->
    // Trager -> gate end to end.
    std::uint64_t st = 0x5EEDC0DEBA5EULL;
    std::size_t proved = 0, total = 0;
    for (int iter = 0; iter < 150; ++iter) {
        using numkit::cas::Rational;
        using numkit::cas::UPoly;
        auto rr = [&](int lim) {
            const std::int64_t q = 1 + static_cast<std::int64_t>(nextU64(st) % 3);
            const std::int64_t p =
                static_cast<std::int64_t>(nextU64(st) % (2 * lim + 1)) - lim;
            return Rational(numkit::cas::BigInt(p), numkit::cas::BigInt(q));
        };
        UPoly den(Rational(std::int64_t{1}));
        const int nLin = static_cast<int>(nextU64(st) % 3);
        const int nQuad = static_cast<int>(nextU64(st) % 2);
        const int nCub = static_cast<int>(nextU64(st) % 2);
        for (int i = 0; i < nLin; ++i) {
            Rational r = rr(5);
            if (r.isZero())
                r = Rational(std::int64_t{1});
            const int m = 1 + static_cast<int>(nextU64(st) % 3);
            den = den * UPoly(std::vector<Rational>{Rational(-r),
                Rational(std::int64_t{1})}).powUInt(m);
        }
        for (int i = 0; i < nQuad; ++i) {
            while (true) {
                const Rational b = rr(4), c = rr(4);
                bool red = false;
                for (std::int64_t r0 = -8; r0 <= 8; ++r0)
                    if (c + b * Rational(r0) + Rational(r0 * r0) == 0)
                        red = true;
                if (!red) {
                    den = den * UPoly(std::vector<Rational>{c, b,
                        Rational(std::int64_t{1})});
                    break;
                }
            }
        }
        for (int i = 0; i < nCub; ++i) {
            while (true) {
                const Rational b = rr(3), c = rr(3);
                bool red = false;
                for (std::int64_t r0 = -8; r0 <= 8; ++r0)
                    if (c + b * Rational(r0) +
                            Rational(r0 * r0 * r0) == 0)
                        red = true;
                if (!red) {
                    den = den * UPoly(std::vector<Rational>{c, b,
                        Rational(std::int64_t{0}), Rational(std::int64_t{1})});
                    break;
                }
            }
        }
        if (den.isConst() || den.deg() < 3)
            continue;
        const int nn = static_cast<int>(nextU64(st) % den.deg());
        std::vector<Rational> ncs;
        for (int i = 0; i <= nn; ++i)
            ncs.push_back(rr(5));
        const UPoly num(ncs);
        if (num.isZero())
            continue;

        numkit::cas::Ctx ctx;
        const numkit::cas::Expr var = ctx.symbol("x");
        const std::string text = ctx.toString(ctx.div(
            numkit::cas::toExpr(ctx, num, var),
            numkit::cas::toExpr(ctx, den, var)));
        ++total;
        const TaskOutcome o = runTask(task("p", "x", text.c_str()));
        if (o.status == TaskStatus::Proved)
            ++proved;
        else
            ADD_FAILURE() << "not proved on: " << text << " (" << o.detail << ")";
    }
    EXPECT_EQ(proved, total);
    EXPECT_GT(total, 100u);
}

// ── layer 3: boundary ──────────────────────────────────────────

TEST(CorpusBoundary, ConstAndDeepTasks)
{
    // Constant task: 7 -> 7*x, proved trivially.
    EXPECT_EQ(runTask(task("c1", "x", "7")).status, TaskStatus::Proved);
    // Non-monic denominator with big multiplicities.
    EXPECT_EQ(runTask(task("c2", "x", "1/(2*x^2 + 2)^3")).status,
              TaskStatus::Proved);
    // Whitespace-heavy but valid text.
    EXPECT_EQ(runTask(task("c3", "x", "  ( 1 ) / ( x + 1 )  ")).status,
              TaskStatus::Proved);
    // Unknown command-like text is just a parse error, never a crash.
    EXPECT_EQ(runTask(task("c4", "x", "integrate x dx")).status,
              TaskStatus::ParseError);
}

} // namespace
