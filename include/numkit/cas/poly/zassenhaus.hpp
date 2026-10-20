// poly/zassenhaus.hpp — factorization of Q[t] polynomials.
#pragma once

#include <numkit/cas/core/budget.hpp>
#include <numkit/cas/num/bigint.hpp>
#include <numkit/cas/poly/upoly.hpp>

#include <vector>

namespace numkit::cas {

// ============================================================
// Zassenhaus factorization over Q:
//   content/primitive split -> mod-p factorization (FpPoly) ->
//   linear Hensel lifting to p^k above the Mignotte bound ->
//   subset reconstruction with exact division over Z.
//
// Everything is deterministic (fixed prime search order, sorted
// subset enumeration).
// ============================================================

// Factor an integer polynomial (degree >= 1, ascending coefficient
// vector) into irreducible factors over Z. The content is stripped
// first — the factors multiply back to the PRIMITIVE part of the
// input. Factors are primitive with positive leading coefficient, in
// a canonical order (by degree, then coefficients). A linear input is
// returned as itself.
std::vector<std::vector<BigInt>>
factorPrimitiveInteger(const std::vector<BigInt> &f, Budget *budget = nullptr);

// Factor any Q[t] polynomial into its content times monic
// irreducible factors. Returns the monic irreducible factors only
// (content dropped, multiplicity kept); zero/constant input yields an
// empty vector.
std::vector<UPoly> factorOverQ(const UPoly &f, Budget *budget = nullptr);

} // namespace numkit::cas
