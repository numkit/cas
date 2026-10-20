// apps/corpus_runner.cpp — corpus machinery implementation.
#include "corpus_runner.hpp"

#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/rubi/rules.hpp>

#include <algorithm>
#include <chrono>
#include <cmath>

namespace nkcorpus {
namespace {

bool isSpace(char ch)
{
    return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

std::string trim(const std::string &s)
{
    std::size_t a = 0, b = s.size();
    while (a < b && isSpace(s[a]))
        ++a;
    while (b > a && isSpace(s[b - 1]))
        --b;
    return s.substr(a, b - a);
}

bool isBlankOrComment(const std::string &raw)
{
    const std::string t = trim(raw);
    return t.empty() || t[0] == '#';
}

} // namespace

LineKind lineKind(const std::string &line)
{
    if (isBlankOrComment(line))
        return LineKind::Skip;
    CorpusTask t;
    return parseCorpusLine(line, t) ? LineKind::Task : LineKind::Malformed;
}

bool parseCorpusLine(const std::string &line, CorpusTask &out)
{
    if (isBlankOrComment(line))
        return false;
    // Two TABs: id<TAB>var<TAB>expr; three TABs:
    // id<TAB>var<TAB>op<TAB>expr (op: integrate | rubi). The expr
    // may contain spaces, but never a TAB.
    const std::size_t t1 = line.find('\t');
    if (t1 == std::string::npos)
        return false;
    const std::size_t t2 = line.find('\t', t1 + 1);
    if (t2 == std::string::npos)
        return false;
    const std::size_t t3 = line.find('\t', t2 + 1);
    if (t3 == std::string::npos) {
        out.id = trim(line.substr(0, t1));
        out.var = trim(line.substr(t1 + 1, t2 - t1 - 1));
        out.expr = trim(line.substr(t2 + 1));
        out.op.clear();
        out.ref.clear();
    } else {
        const std::size_t t4 = line.find('\t', t3 + 1);
        if (t4 == std::string::npos) {
            out.id = trim(line.substr(0, t1));
            out.var = trim(line.substr(t1 + 1, t2 - t1 - 1));
            out.op = trim(line.substr(t2 + 1, t3 - t2 - 1));
            out.expr = trim(line.substr(t3 + 1));
            out.ref.clear();
        } else {
            if (line.find('\t', t4 + 1) != std::string::npos)
                return false;
            out.id = trim(line.substr(0, t1));
            out.var = trim(line.substr(t1 + 1, t2 - t1 - 1));
            out.op = trim(line.substr(t2 + 1, t3 - t2 - 1));
            out.expr = trim(line.substr(t3 + 1, t4 - t3 - 1));
            out.ref = trim(line.substr(t4 + 1));
            if (out.op.empty() || out.ref.empty())
                return false;
        }
    }
    return !out.id.empty() && !out.var.empty() && !out.expr.empty();
}

std::uint64_t medianOf(std::vector<std::uint64_t> vals)
{
    if (vals.empty())
        return 0;
    std::sort(vals.begin(), vals.end());
    const std::size_t n = vals.size();
    if (n % 2 == 1)
        return vals[n / 2];
    // even: mean of the two middle values, rounded up
    return (vals[n / 2 - 1] + vals[n / 2] + 1) / 2;
}

std::uint64_t percentileOf(std::vector<std::uint64_t> vals, double p)
{
    if (vals.empty() || p <= 0.0 || p > 1.0)
        return 0;
    std::sort(vals.begin(), vals.end());
    // nearest-rank: the ceil(p*n)-th smallest
    const std::size_t rank = static_cast<std::size_t>(
        std::ceil(p * static_cast<double>(vals.size())));
    return vals[std::min(rank, vals.size()) - 1];
}

TaskOutcome runTask(const CorpusTask &t)
{
    using Clock = std::chrono::steady_clock;
    TaskOutcome o;
    o.id = t.id;
    numkit::cas::Ctx ctx;
    const auto start = Clock::now();
    try {
        const numkit::cas::Expr f = numkit::cas::parseExpr(ctx, t.expr);
        const numkit::cas::Expr var = ctx.symbol(t.var);
        bool proved = false;
        numkit::cas::Expr F;
        std::string reason;
        if (t.op == "rubi") {
            // The C2 rule engine: certified rule application of the
            // committed slice.
            F = numkit::cas::rubi::rubiApply(
                numkit::cas::rubi::sliceTables(), ctx, f, var);
            proved = !F.isNull();
            if (!proved)
                reason = "no certified rule application";
        } else if (t.op == "cascade") {
            const numkit::cas::RationalIntegral r =
                numkit::cas::integrate(ctx, f, var);
            proved = r.proved();
            F = r.F;
            reason = r.reason;
        } else {
            const numkit::cas::RationalIntegral r =
                numkit::cas::integrateRational(ctx, f, var);
            proved = r.proved();
            F = r.F;
            reason = r.reason;
        }
        const auto stop = Clock::now();
        o.micros = static_cast<std::uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(stop - start)
                .count());
        if (proved) {
            o.status = TaskStatus::Proved;
            o.answerNodes = ctx.nodeCount();
            o.answerLeaves = ctx.leafCount(F);
            if (!t.ref.empty()) {
                const numkit::cas::Expr refExpr =
                    numkit::cas::parseExpr(ctx, t.ref);
                o.refLeaves = ctx.leafCount(refExpr);
                if (o.refLeaves > 0) {
                    o.leafRatio = static_cast<double>(o.answerLeaves) /
                                  static_cast<double>(o.refLeaves);
                }
            }
        } else {
            o.status = TaskStatus::Unevaluated;
            o.detail = reason.empty() ? "declined" : reason;
        }
    } catch (const numkit::cas::ParseError &e) {
        const auto stop = Clock::now();
        o.micros = static_cast<std::uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(stop - start)
                .count());
        o.status = TaskStatus::ParseError;
        o.detail = e.what();
    }
    return o;
}

double CorpusReport::passRatePct() const
{
    if (total == 0)
        return 0.0;
    return 100.0 * static_cast<double>(proved) / static_cast<double>(total);
}

double CorpusReport::verificationRatePct() const
{
    const std::size_t denom = proved + unevaluated;
    if (denom == 0)
        return 0.0;
    return 100.0 * static_cast<double>(proved) / static_cast<double>(denom);
}

CorpusReport runCorpus(const std::vector<CorpusTask> &tasks,
                       std::vector<TaskOutcome> *outcomes)
{
    CorpusReport rep;
    rep.total = tasks.size();
    std::vector<std::uint64_t> times;
    times.reserve(tasks.size());
    double leafRatioSum = 0.0;
    for (const CorpusTask &t : tasks) {
        TaskOutcome o = runTask(t);
        switch (o.status) {
        case TaskStatus::Proved:
            ++rep.proved;
            if (o.refLeaves > 0) {
                ++rep.withReference;
                leafRatioSum += o.leafRatio;
            }
            break;
        case TaskStatus::Unevaluated: ++rep.unevaluated; break;
        case TaskStatus::ParseError: ++rep.parseErrors; break;
        case TaskStatus::MalformedLine: ++rep.malformedLines; break;
        }
        times.push_back(o.micros);
        if (outcomes != nullptr)
            outcomes->push_back(std::move(o));
    }
    rep.medianMicros = medianOf(times);
    rep.p95Micros = percentileOf(times, 0.95);
    rep.meanLeafRatio = rep.withReference > 0
                            ? leafRatioSum / static_cast<double>(rep.withReference)
                            : 0.0;
    return rep;
}

} // namespace nkcorpus
