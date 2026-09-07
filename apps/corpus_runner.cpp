// apps/corpus_runner.cpp — corpus machinery implementation.
#include "corpus_runner.hpp"

#include <numkit/cas/core/parser.hpp>
#include <numkit/cas/integrate/ratint.hpp>

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
    // Exactly two TABs: id<TAB>var<TAB>expr (expr may contain spaces,
    // but never a TAB — that is what separates the columns).
    const std::size_t t1 = line.find('\t');
    if (t1 == std::string::npos)
        return false;
    const std::size_t t2 = line.find('\t', t1 + 1);
    if (t2 == std::string::npos)
        return false;
    if (line.find('\t', t2 + 1) != std::string::npos)
        return false;
    out.id = trim(line.substr(0, t1));
    out.var = trim(line.substr(t1 + 1, t2 - t1 - 1));
    out.expr = trim(line.substr(t2 + 1));
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
        const numkit::cas::RationalIntegral r = numkit::cas::integrateRational(
            ctx, f, ctx.symbol(t.var));
        const auto stop = Clock::now();
        o.micros = static_cast<std::uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(stop - start)
                .count());
        if (r.proved()) {
            o.status = TaskStatus::Proved;
            o.answerNodes = ctx.nodeCount();
        } else {
            o.status = TaskStatus::Unevaluated;
            o.detail = r.reason;
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
    for (const CorpusTask &t : tasks) {
        TaskOutcome o = runTask(t);
        switch (o.status) {
        case TaskStatus::Proved: ++rep.proved; break;
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
    return rep;
}

} // namespace nkcorpus
