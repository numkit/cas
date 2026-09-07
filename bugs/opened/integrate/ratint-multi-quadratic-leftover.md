# ratint-multi-quadratic-leftover

Kind: bug
Status: OPEN
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
