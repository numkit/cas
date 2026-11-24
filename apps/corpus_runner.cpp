// apps/corpus_runner.cpp — corpus machinery implementation.
#include <keel/algo.h>
#include <keel/core.h>
#include <keel/time.h>
#include "corpus_runner.hpp"

#include <numkit/cas/parse_expr.hpp>
#include <keel/cas/integrate/ratint.hpp>
#include <keel/cas/rubi/rules.hpp>

#include <algorithm>
#include <cmath>

namespace nkcorpus {
namespace {

bool isSpace(char ch)
{
    return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

keel::StringRef trimRef(keel::StringRef s)
{
    keel::usize a = 0, b = s.size();
    while (a < b && isSpace(s[a]))
        ++a;
    while (b > a && isSpace(s[b - 1]))
        --b;
    return s.substr(a, b - a);
}

bool isBlankOrComment(keel::StringRef raw)
{
    const keel::StringRef t = trimRef(raw);
    return t.empty() || t[0] == '#';
}

} // namespace

LineKind lineKind(keel::StringRef line)
{
    if (isBlankOrComment(line))
        return LineKind::Skip;
    CorpusTask t;
    return parseCorpusLine(line, t) ? LineKind::Task : LineKind::Malformed;
}

bool parseCorpusLine(keel::StringRef line, CorpusTask &out)
{
    if (isBlankOrComment(line))
        return false;
    // Two TABs: id<TAB>var<TAB>expr; three TABs:
    // id<TAB>var<TAB>op<TAB>expr (op: integrate | rubi). The expr
    // may contain spaces, but never a TAB.
    const keel::usize t1 = line.find('\t');
    if (t1 == keel::kInvalidIndex)
        return false;
    const keel::usize t2 = line.find('\t', t1 + 1);
    if (t2 == keel::kInvalidIndex)
        return false;
    const keel::usize t3 = line.find('\t', t2 + 1);
    if (t3 == keel::kInvalidIndex) {
        out.id.assign(trimRef(line.substr(0, t1)));
        out.var.assign(trimRef(line.substr(t1 + 1, t2 - t1 - 1)));
        out.expr.assign(trimRef(line.substr(t2 + 1)));
        out.op.clear();
        out.ref.clear();
    } else {
        const keel::usize t4 = line.find('\t', t3 + 1);
        if (t4 == keel::kInvalidIndex) {
            out.id.assign(trimRef(line.substr(0, t1)));
            out.var.assign(trimRef(line.substr(t1 + 1, t2 - t1 - 1)));
            out.op.assign(trimRef(line.substr(t2 + 1, t3 - t2 - 1)));
            out.expr.assign(trimRef(line.substr(t3 + 1)));
            out.ref.clear();
        } else {
            if (line.find('\t', t4 + 1) != keel::kInvalidIndex)
                return false;
            out.id.assign(trimRef(line.substr(0, t1)));
            out.var.assign(trimRef(line.substr(t1 + 1, t2 - t1 - 1)));
            out.op.assign(trimRef(line.substr(t2 + 1, t3 - t2 - 1)));
            out.expr.assign(trimRef(line.substr(t3 + 1, t4 - t3 - 1)));
            out.ref.assign(trimRef(line.substr(t4 + 1)));
            if (out.op.empty() || out.ref.empty())
                return false;
        }
    }
    return !out.id.empty() && !out.var.empty() && !out.expr.empty();
}

keel::u64 medianOf(keel::ArrayRef<keel::u64> valsIn)
{
    if (valsIn.empty())
        return 0;
    keel::Array<keel::u64> vals = keel::Array<keel::u64>::from(valsIn);
    keel::sort(vals);
    const keel::usize n = vals.size();
    if (n % 2 == 1)
        return vals[n / 2];
    // even: mean of the two middle values, rounded up
    return (vals[n / 2 - 1] + vals[n / 2] + 1) / 2;
}

keel::u64 percentileOf(keel::ArrayRef<keel::u64> valsIn, double p)
{
    if (valsIn.empty() || p <= 0.0 || p > 1.0)
        return 0;
    keel::Array<keel::u64> vals = keel::Array<keel::u64>::from(valsIn);
    keel::sort(vals);
    // nearest-rank: the ceil(p*n)-th smallest
    const keel::usize rank = static_cast<keel::usize>(
        std::ceil(p * static_cast<double>(vals.size())));
    return vals[std::min(rank, vals.size()) - 1];
}

TaskOutcome runTask(const CorpusTask &t)
{
    TaskOutcome o;
    o.id = t.id.clone();
    keel::cas::Ctx ctx;
    const keel::u64 startNs = keel::monotonic_ns();
    try {
        const keel::cas::Expr f = numkit::cas::parseExpr(ctx, t.expr);
        const keel::cas::Expr var = ctx.symbol(t.var);
        bool proved = false;
        keel::cas::Expr F;
        keel::String reason;
        if (t.op == "rubi") {
            // The C2 rule engine: certified rule application of the
            // committed slice.
            F = keel::cas::rubi::rubiApply(
                keel::cas::rubi::sliceTables(), ctx, f, var);
            proved = !F.isNull();
            if (!proved)
                reason.assign("no certified rule application");
        } else if (t.op == "cascade") {
            keel::cas::RationalIntegral r =
                keel::cas::integrate(ctx, f, var);
            proved = r.proved();
            F = r.F;
            reason = keel::move(r.reason);
        } else {
            keel::cas::RationalIntegral r =
                keel::cas::integrateRational(ctx, f, var);
            proved = r.proved();
            F = r.F;
            reason = keel::move(r.reason);
        }
        const keel::u64 stopNs = keel::monotonic_ns();
        o.micros = (stopNs >= startNs) ? (stopNs - startNs) / 1000ULL : 0ULL;
        if (proved) {
            o.status = TaskStatus::Proved;
            o.answerNodes = ctx.nodeCount();
            o.answerLeaves = ctx.leafCount(F);
            if (!t.ref.empty()) {
                const keel::cas::Expr refExpr =
                    numkit::cas::parseExpr(ctx, t.ref);
                o.refLeaves = ctx.leafCount(refExpr);
                if (o.refLeaves > 0) {
                    o.leafRatio = static_cast<double>(o.answerLeaves) /
                                  static_cast<double>(o.refLeaves);
                }
            }
        } else {
            o.status = TaskStatus::Unevaluated;
            o.detail = reason.empty() ? keel::String::from("declined") : keel::move(reason);
        }
    } catch (const numkit::cas::ParseError &e) {
        const keel::u64 stopNs = keel::monotonic_ns();
        o.micros = (stopNs >= startNs) ? (stopNs - startNs) / 1000ULL : 0ULL;
        o.status = TaskStatus::ParseError;
        o.detail.assign(e.what());
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
    const keel::usize denom = proved + unevaluated;
    if (denom == 0)
        return 0.0;
    return 100.0 * static_cast<double>(proved) / static_cast<double>(denom);
}

CorpusReport runCorpus(keel::ArrayRef<CorpusTask> tasks,
                       keel::Array<TaskOutcome> *outcomes)
{
    CorpusReport rep;
    rep.total = tasks.size();
    keel::Array<keel::u64> times;
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
            outcomes->push_back(keel::move(o));
    }
    rep.medianMicros = medianOf(times);
    rep.p95Micros = percentileOf(times, 0.95);
    rep.meanLeafRatio = rep.withReference > 0
                            ? leafRatioSum / static_cast<double>(rep.withReference)
                            : 0.0;
    return rep;
}

} // namespace nkcorpus
