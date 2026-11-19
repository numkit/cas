// apps/corpus_runner.hpp — corpus machinery for the §7 CI audit.
//
// This is CI/CLI infrastructure, NOT part of the vendored library:
// it lives in apps/ and is compiled directly into the nkcas binary
// and into the gtest binary (which adds the sources), so the core
// stays free of corpus concerns.
#pragma once

#include <keel/array.h>
#include <keel/core.h>
#include <keel/string.h>
#include <cstddef>
#include <cstdint>

namespace nkcorpus {

// One corpus task, parsed from "id<TAB>var<TAB>expr", the 4-column
// form "id<TAB>var<TAB>op<TAB>expr" (op: integrate | rubi | cascade),
// or the 5-column form "id<TAB>var<TAB>op<TAB>expr<TAB>ref" where ref
// is the reference antiderivative for Mean Leaf Ratio (MLR) auditing.
struct CorpusTask {
    keel::String id;
    keel::String var;
    keel::String expr;
    keel::String op;  // "rubi" routes through the rule engine, "cascade" through integrate()
    keel::String ref; // optional reference antiderivative (5-column format)

    CorpusTask() noexcept = default;
    CorpusTask(keel::StringRef id_, keel::StringRef var_, keel::StringRef expr_,
               keel::StringRef op_ = {}, keel::StringRef ref_ = {})
        : id(keel::String::from(id_)), var(keel::String::from(var_)),
          expr(keel::String::from(expr_)), op(keel::String::from(op_)),
          ref(keel::String::from(ref_))
    {
    }
    CorpusTask(const CorpusTask &o)
        : id(o.id.clone()), var(o.var.clone()), expr(o.expr.clone()),
          op(o.op.clone()), ref(o.ref.clone())
    {
    }
    CorpusTask &operator=(const CorpusTask &o)
    {
        if (this != &o) {
            id = o.id.clone();
            var = o.var.clone();
            expr = o.expr.clone();
            op = o.op.clone();
            ref = o.ref.clone();
        }
        return *this;
    }
    CorpusTask(CorpusTask &&) noexcept = default;
    CorpusTask &operator=(CorpusTask &&) noexcept = default;
};

enum class TaskStatus {
    Proved,        // integrateRational returned a certified answer
    Unevaluated,   // parsed fine, integrator declined (honest)
    ParseError,    // malformed expression text
    MalformedLine, // the corpus line itself is broken
};

struct TaskOutcome {
    keel::String id;
    TaskStatus status = TaskStatus::MalformedLine;
    keel::String detail;           // reason / error message
    keel::u64 micros = 0;     // parse+integrate wall time
    keel::usize answerNodes = 0;  // Ctx node count after a proved run
    keel::usize answerLeaves = 0; // Ctx::leafCount(F) after a proved run
    keel::usize refLeaves = 0;    // Ctx::leafCount(ref) when ref is provided
    double leafRatio = 0.0;       // answerLeaves / refLeaves when refLeaves > 0
};

struct CorpusReport {
    keel::usize total = 0;
    keel::usize proved = 0;
    keel::usize unevaluated = 0;
    keel::usize parseErrors = 0;
    keel::usize malformedLines = 0;
    keel::u64 medianMicros = 0;
    keel::u64 p95Micros = 0;
    keel::usize withReference = 0;
    double meanLeafRatio = 0.0;

    // proved / total, in percent (0 when total == 0).
    double passRatePct() const;
    // proved / (proved + unevaluated): of the tasks that parsed and
    // reached the integrator, how many carry a certificate (0 when
    // the denominator is 0 — all-parse-error corpora are not "0%
    // verified", they are unmeasurable).
    double verificationRatePct() const;
};

// Parse one corpus line. Blank lines and '#' comments yield false
// without touching `out`; structurally broken lines yield false too
// (the caller counts them separately by re-checking the raw line —
// see lineKind()). Fields are trimmed; inner spaces survive in expr.
bool parseCorpusLine(keel::StringRef line, CorpusTask &out);

// Classify a raw corpus line without producing a task.
enum class LineKind { Task, Skip, Malformed };
LineKind lineKind(keel::StringRef line);

// Deterministic order statistics. medianOf: middle value; for an even
// count the mean of the two middle values rounded up. percentileOf:
// nearest-rank, p in (0, 1].
keel::u64 medianOf(keel::ArrayRef<keel::u64> vals);
keel::u64 percentileOf(keel::ArrayRef<keel::u64> vals, double p);

// Run one task end to end: parse -> integrate -> certificate check.
TaskOutcome runTask(const CorpusTask &t);

// Run all tasks, filling per-task outcomes when requested.
CorpusReport runCorpus(keel::ArrayRef<CorpusTask> tasks,
                       keel::Array<TaskOutcome> *outcomes = nullptr);

} // namespace nkcorpus
