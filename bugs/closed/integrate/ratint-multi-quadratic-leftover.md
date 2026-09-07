# ratint-multi-quadratic-leftover

Kind: bug
Status: ✅ FIXED (cee8e9d narrowed, this change closed)
Area: integrate

## Description

With the factorized residue pipeline (factorOverQ on the squarefree
resultant + per-quadratic modular Trager loop), an integrand whose
denominator has ONE linear and TWO irreducible quadratic factors
leaves an unconsumed leftover: the quadratic loop's subtractions do
not zero out leftN, and the final integrateSplitting fallback rejects
the degree-4 leftover with "irreducible factor of degree > 2".

## Repro

```
N = x^3 + 5x^2 - 3x - 2
D = (x + 2/3)(x^2 - x + 3)(x^2 + x/4 + 4)
   = 8 + 59/6 x + 5/4 x^2 + 25/4 x^3 - 1/12 x^4 + x^5
integrateRational(N/D)
```

Actual: Unevaluated "irreducible factor of degree > 2 (needs algebraic
residues)". Expected: PROVED_SYMBOLIC (residues at the two conjugate
pole pairs are quadratic irrationalities; sqrtExpr covers them).

Single-quadratic denominators work (x^2+2)(x^2+3) case passes), so the
per-factor gcd v = gcd(A - tS', S) over Q[t]/(c_i) and the pair
subtraction are individually correct; the multi-factor interaction
(subtraction bookkeeping across loop iterations, or Rsq2 of the
REDUCED leftover regenerating already-consumed factors) is the suspect.

## Guard

RatIntTest.DISABLED_MultipleQuadraticResidueFactors (property body;
the fixed vector inside it documents the exact case).

Impact: coverage regression risk is none vs main (main could not
produce these answers at all); the bug blocks the C1 completion
criterion "any rational function with residues in quadratic
extensions".

## 2026-09-08 session findings (precise narrowing)

- The integrator-side machinery is NOT the cause: the quadratic loop
  never even ran for the repro — factorOverQ(Rsq2) returned the
  degree-5 squarefree resultant WHOLE (single factor), so no quadratic
  factors were ever presented to the loop.
- FpPoly::factor is correct on the mod-19 image (roots {3,7,18};
  factors d1 d1 d1 d2 — verified by an isolated debug test).
- Hensel invariants hold (Debug run of the repro: no assert fired).
- Remaining suspect: the subset/divisor reconstruction inside
  factorPrimitiveInteger for THIS input — integer primitive poly
  [-10389627032015, 0, 23275963107408, -988346505344,
  -18826327357440, 2043157708800], p = 19, 4 lifted factors,
  lc = 2043157708800. Next session: dump divisorsOf(lc) and each
  subset-divisor candidate for this exact case.
- Additionally fixed this session (kept): the integrator's quadratic
  loop now breaks when the running numerator hits zero mid-loop —
  gcd(0 - t*S', S) can be nontrivial in Q[t]/(c) and subtracting its
  contribution resurrects a zero numerator, producing garbage leftover
  (a real bug caught by the diagnostics, distinct from the main one).

## CLOSURE

Root cause (found one session after the narrowing): the subset/divisor
reconstruction enumerated the leading coefficient's divisors under a
40-BIT CAP — a crutch from the early implementation. The repro's
leading coefficient 2043157708800 is exactly 41 bits, so the divisor
list collapsed to {1, lc}, every proper leading-coefficient divisor
(3, 9, ...) was never tried, no subset divided exactly, and the honest
fallback returned the whole polynomial — which surfaced upstream as the
multi-quadratic integrator receiving an unfactored resultant.

Fix: the cap is removed; divisor enumeration is a clean divisorsOf
helper (trial division against the SHRINKING cofactor, so smooth
coefficients finish fast). Known cost, documented in notes: a leading
coefficient with a large prime factor P costs sqrt(P) BigInt
divisions — acceptable at current scales, Pollard-rho if it ever
bites.

Guard: ZassenhausFixed.Classics et al. plus the enabled
RatIntTest.MultipleQuadraticResidueFactors (the 500-case property
with two irreducible non-square quadratics and mixed linears, all
PROVED_SYMBOLIC). All 89 tests green.
