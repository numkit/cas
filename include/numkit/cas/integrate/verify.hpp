// integrate/verify.hpp — Tier-2a: certified interval audit of the FORM.
#pragma once

#include <numkit/cas/core/expr.hpp>

namespace numkit::cas {

// ============================================================
// Tier-2a form check (plan D-series): after the Tier-1 polynomial
// certificate proves that the SUM OF PIECE DERIVATIVES equals the
// integrand in Q(x), the assembled FORM F itself may still be wrong
// (the Rioboo x2-w2 incident: PROVED with a twice-wrong printed
// form). This check closes the gap at runtime: dF/dvar and the
// integrand are evaluated as EXACT RATIONAL ENCLOSURES at several
// rational sample points - RootOf atoms contribute their isolating
// intervals (Sturm), rational powers enclose via bisection roots -
// so disjoint enclosures are a PROVEN mismatch, never an artifact
// of overestimation.
//
//   Match     - >= 3 sample points compared, all compatible;
//   Mismatch  - some point has provably disjoint enclosures
//               (a certified form bug - the caller must decline);
//   Unknown   - transcendental atoms (exp/log/sin), unevaluable
//               exponents/bases, or too few valid samples; the
//               storeys carry their own gates for those.
//
// No floating point anywhere: intervals are Rational bounds with
// outward semantics; division by an interval containing zero and
// rational powers of intervals crossing zero decline (Unknown).
enum class Tier2aStatus
{
    Match,
    Mismatch,
    Unknown,
};

Tier2aStatus tier2aFormCheck(Ctx &c, Expr F, Expr f, Expr var);

} // namespace numkit::cas
