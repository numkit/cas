// core/budget.hpp — cancellation/budget token for long-running algorithms.
#pragma once

#include <cstdint>

namespace numkit::cas {

// ============================================================
// Budget — the day-one cancellation plumbing (per the M0 decisions).
// Every user-facing algorithm thread this through its loops so the
// future speculative cascade (plan D9) can abort heavy branches.
// steps < 0 means unlimited (the default for pure-math callers whose
// loops are structurally terminating).
// ============================================================
struct Budget
{
    std::int64_t steps = -1;

    bool unlimited() const { return steps < 0; }

    // Consume one step; false means the budget is exhausted and the
    // algorithm must return its honest "not finished" outcome.
    bool tryConsume()
    {
        if (steps < 0)
            return true;
        if (steps == 0)
            return false;
        --steps;
        return true;
    }
};

} // namespace numkit::cas
