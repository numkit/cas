// core/budget.hpp — cancellation/budget token for long-running algorithms.
#pragma once

#include <keel/core.h>
#include <cstddef>
#include <cstdint>

namespace numkit::cas {

enum class BudgetStatus : keel::u8
{
    Ok = 0,
    StepExhausted = 1,
    ArenaExhausted = 2,
};

// ============================================================
// Budget — the day-one cancellation plumbing (per the M0 decisions).
// Every user-facing algorithm threads this through its loops so the
// speculative cascade (plan D9 / C1 item 34) can abort heavy branches.
// steps < 0 means unlimited steps; maxArenaBytes == 0 means unlimited
// arena memory.
// ============================================================
struct Budget
{
    keel::i64 steps = -1;
    keel::usize maxArenaBytes = 0;
    keel::usize stepsUsed_ = 0;
    keel::usize arenaBytesUsed_ = 0;
    BudgetStatus status_ = BudgetStatus::Ok;

    Budget() = default;
    explicit Budget(keel::i64 maxSteps, keel::usize maxArena = 0)
        : steps(maxSteps), maxArenaBytes(maxArena)
    {
    }

    bool unlimited() const { return steps < 0 && maxArenaBytes == 0; }
    bool ok() const noexcept { return status_ == BudgetStatus::Ok; }
    BudgetStatus status() const noexcept { return status_; }
    keel::usize stepsUsed() const noexcept { return stepsUsed_; }
    keel::usize arenaBytesUsed() const noexcept { return arenaBytesUsed_; }

    // Consume one step; false means the budget is exhausted and the
    // algorithm must return its honest "not finished" outcome.
    bool tryConsume() noexcept
    {
        if (status_ != BudgetStatus::Ok)
            return false;
        if (steps == 0) {
            status_ = BudgetStatus::StepExhausted;
            return false;
        }
        if (steps > 0)
            --steps;
        ++stepsUsed_;
        return true;
    }

    bool step() noexcept { return tryConsume(); }

    bool recordArenaBytes(keel::usize bytes) noexcept
    {
        if (status_ != BudgetStatus::Ok)
            return false;
        if (bytes > arenaBytesUsed_)
            arenaBytesUsed_ = bytes;
        if (maxArenaBytes > 0 && arenaBytesUsed_ > maxArenaBytes) {
            status_ = BudgetStatus::ArenaExhausted;
            return false;
        }
        return true;
    }
};

} // namespace numkit::cas
