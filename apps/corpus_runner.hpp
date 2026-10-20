// apps/corpus_runner.hpp — corpus machinery for the §7 CI audit.
//
// This is CI/CLI infrastructure, NOT part of the vendored library:
// it lives in apps/ and is compiled directly into the nkcas binary
// and into the gtest binary (which adds the sources), so the core
// stays free of corpus concerns.
#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace nkcorpus {

// One corpus task, parsed from "id<TAB>var<TAB>expr", the 4-column
// form "id<TAB>var<TAB>op<TAB>expr" (op: integrate | rubi | cascade),
// or the 5-column form "id<TAB>var<TAB>op<TAB>expr<TAB>ref" where ref
// is the reference antiderivative for Mean Leaf Ratio (MLR) auditing.
struct CorpusTask {
    std::string id;
    std::string var;
    std::string expr;
    std::string op;  // "rubi" routes through the rule engine, "cascade" through integrate()
    std::string ref; // optional reference antiderivative (5-column format)
};

enum class TaskStatus {
    Proved,        // integrateRational returned a certified answer
    Unevaluated,   // parsed fine, integrator declined (honest)
    ParseError,    // malformed expression text
    MalformedLine, // the corpus line itself is broken
};

struct TaskOutcome {
    std::string id;
    TaskStatus status = TaskStatus::MalformedLine;
    std::string detail;           // reason / error message
    std::uint64_t micros = 0;     // parse+integrate wall time
    std::size_t answerNodes = 0;  // Ctx node count after a proved run
    std::size_t answerLeaves = 0; // Ctx::leafCount(F) after a proved run
    std::size_t refLeaves = 0;    // Ctx::leafCount(ref) when ref is provided
    double leafRatio = 0.0;       // answerLeaves / refLeaves when refLeaves > 0
};

struct CorpusReport {
    std::size_t total = 0;
    std::size_t proved = 0;
    std::size_t unevaluated = 0;
    std::size_t parseErrors = 0;
    std::size_t malformedLines = 0;
    std::uint64_t medianMicros = 0;
    std::uint64_t p95Micros = 0;
    std::size_t withReference = 0;
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
bool parseCorpusLine(const std::string &line, CorpusTask &out);

// Classify a raw corpus line without producing a task.
enum class LineKind { Task, Skip, Malformed };
LineKind lineKind(const std::string &line);

// Deterministic order statistics. medianOf: middle value; for an even
// count the mean of the two middle values rounded up. percentileOf:
// nearest-rank, p in (0, 1].
std::uint64_t medianOf(std::vector<std::uint64_t> vals);
std::uint64_t percentileOf(std::vector<std::uint64_t> vals, double p);

// Run one task end to end: parse -> integrate -> certificate check.
TaskOutcome runTask(const CorpusTask &t);

// Run all tasks, filling per-task outcomes when requested.
CorpusReport runCorpus(const std::vector<CorpusTask> &tasks,
                       std::vector<TaskOutcome> *outcomes = nullptr);

} // namespace nkcorpus
