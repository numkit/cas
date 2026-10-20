// core/budget.hpp — cancellation/budget token for long-running algorithms.
#pragma once

#include <cstddef>
#include <cstdint>

namespace numkit::cas {

enum class BudgetStatus : std::uint8_t
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
    std::int64_t steps = -1;
    std::size_t maxArenaBytes = 0;
    std::size_t stepsUsed_ = 0;
    std::size_t arenaBytesUsed_ = 0;
    BudgetStatus status_ = BudgetStatus::Ok;

    Budget() = default;
    explicit Budget(std::int64_t maxSteps, std::size_t maxArena = 0)
        : steps(maxSteps), maxArenaBytes(maxArena)
    {
    }

    bool unlimited() const { return steps < 0 && maxArenaBytes == 0; }
    bool ok() const noexcept { return status_ == BudgetStatus::Ok; }
    BudgetStatus status() const noexcept { return status_; }
    std::size_t stepsUsed() const noexcept { return stepsUsed_; }
    std::size_t arenaBytesUsed() const noexcept { return arenaBytesUsed_; }

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

    bool recordArenaBytes(std::size_t bytes) noexcept
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
