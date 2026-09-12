# tier2a-zero-divisor-fractional-pow

Kind: bug
Status: ✅ FIXED (v0.1.0 release change, 2026-09-12)
Area: integrate

## Description

Two interacting defects in the Tier-2a interval audit
(`src/integrate/verify.cpp`), found during the v0.1.0 release gate
(a Debug-binary ctest pass; the Release binaries masked both):

1. **qRoot bisected toward the WRONG root for non-integer
   rationals.** The comparison used `mid.num^q * r.den^q <=
   r.num * mid.den^q`, i.e. tested `mid^q <= r/r.den^(q-1)` instead
   of `mid^q <= r` — correct only for integer `r` (den = 1). Every
   fractional radical of a non-integer rational got a wrong
   enclosure; when the wrong threshold sat beyond the 24-step
   bisection reach, the returned enclosure kept `lo = 0`.
2. **Negative fractional powers divided by zero-lower-end
   enclosures.** `iPowRatPos` with `p < 0` called `iDiv` on the
   powered enclosure without checking its lower end: `iDiv`'s
   `assert(!containsZero(b))` aborted in Debug, and Release divided
   by zero (silent UB that only appeared to "pass" because the
   garbage interval degraded the audit to an implicit skip).

Impact: 5 RatInt property tests crashed in Debug
(`RatIntTest.MultipleQuadraticResidueFactors` + four more in the
ctest 129–166 range, e.g. TanRational/Radical/C1Completeness
neighbors); in Release the audit's discriminative power on
radical-containing forms was silently degraded (both sides of the
comparison shared the same wrong enclosures, so no false Mismatch
appeared — Tier-1 remained the true gate, and no wrong answer ever
passed: verified by 500/500 + 120/120 after the fix).

## Repro

Debug build, `ctest -C Debug -R RatIntTest`:
`Assertion failed: !containsZero(b), file src/integrate/verify.cpp,
line 51` before the fix. Direct shape: the pair
`f = x^59 * (x^60)^(-1/2)`, `F = (1/30) * (x^60)^(1/2)` at the
sample point x0 = 1/2 (base 2^-60; both defects fire).

## Root cause

Wrong cross-multiplication exponent in the bisection predicate
(`r.den^q` instead of `r.den` — the historical hi.den→mid.den fix
of d1bd806 corrected a different factor of the same comparison and
left this one in), plus a missing zero-lower-end guard before the
reciprocal in `iPowRatPos`.

## Fix

- qRoot predicate: `mid.num^q * r.den <= r.num * mid.den^q`.
- `iPowRatPos` returns bool and declines (sample point skipped,
  honest-Unknown flow) when `p < 0` and the powered enclosure has a
  zero lower end.

## Guard

`RatIntTest.Tier2aTinyBaseFractionalPower` (two vectors: k=30 must
be Match — catches the wrong-root defect, it used to collapse to
Unknown; k=60 must be Unknown without crashing — catches the
zero-divisor division, it used to abort in Debug), plus the five
previously Debug-crashing property tests now green in Debug.
