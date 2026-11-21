// poly/solve.hpp — exact polynomial solving over the reals.
#pragma once

#include <keel/array.h>
#include <numkit/cas/poly/sturm.hpp>
#include <numkit/cas/poly/upoly.hpp>

namespace numkit::cas {

// ============================================================
// Real roots of a non-zero polynomial with rational coefficients,
// exact: rational roots come back as exact values (recognized via
// the full factorization), irrational roots as (carrier, index,
// isolating interval) triples — the carrier is the monic squarefree
// part carrying the root, index counts among the carrier's REAL
// roots in ascending order, and the interval is the Sturm-isolated
// (lo, hi] bracket, refinable by refineRoot().
//
// Deliberately NO Expr/RootOf nodes here: the integrator's RootOf
// atoms index ALL conjugate embeddings, a different numbering —
// conflating the two would be a silent semantics bug (see
// notes/c1-algebraic-layer.md, item 21).
// ============================================================
struct RealRootSolution
{
    bool isRational = false;
    Rational value;        // exact, when isRational
    UPoly carrier;         // monic squarefree carrier polynomial
    keel::i32 realIndex = 0;     // 0-based among the carrier's real roots
    RootInterval interval; // isolating bracket; exact() == isRational
};

// All distinct real roots of p, ascending. Requires p != 0.
keel::Array<RealRootSolution> solveRealRoots(const UPoly &p);

} // namespace numkit::cas
