// poly/sturm.hpp — real root isolation over Q via Sturm sequences.
#pragma once

#include <numkit/cas/poly/upoly.hpp>

#include <utility>
#include <vector>

namespace numkit::cas {

// ============================================================
// Sturm machinery for a squarefree polynomial with rational
// coefficients. All arithmetic is exact.
//
// RootInterval: open interval (lo, hi) containing exactly one root;
// lo == hi encodes an exact rational root (found when a bisection
// midpoint lands on it).
// ============================================================
struct RootInterval
{
    Rational lo;
    Rational hi;
    bool exact() const { return lo == hi; }
};

// Classical Sturm chain: s0 = p, s1 = p', s_{k+1} = -(s_{k-1} mod s_k).
std::vector<UPoly> sturmSequence(const UPoly &p);

// Cauchy root bound: every complex root z of p satisfies |z| < B.
Rational cauchyRootBound(const UPoly &p);

// Number of distinct real roots of the chain polynomial in the
// HALF-OPEN interval (a, b] (skip-zero variations: V(a) - V(b)).
// Endpoints may be roots; a strict count needs the a/b root status
// tracked by the caller.
std::size_t countRealRoots(const std::vector<UPoly> &sturm,
                           const Rational &a, const Rational &b);

// Isolate all distinct real roots of p (multiplicities ignored; p is
// reduced to its squarefree part internally). Returns pairwise disjoint
// intervals, each containing exactly one root, ordered by position.
std::vector<RootInterval> isolateRealRoots(const UPoly &p);

// Bisect one interval until its width is below the target; the root of
// the squarefree p stays inside. Exact roots are returned unchanged.
RootInterval refineRoot(const UPoly &p, RootInterval iv,
                        const Rational &targetWidth);

} // namespace numkit::cas
