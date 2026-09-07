# zassenhaus-cubic-cofactor-unsplit

Kind: bug
Status: OPEN
Area: poly

## Description

`factorOverQ` on 27x^4 - 54x^3 - 144x^2 - 16x + 320 returns
[x - 4/3] and the whole cubic x^3 - 2/3x^2 - 56/9x - 80/9, but the
cubic factors further over Q as (x - 10/3)(x^2 + 8/3x + 8/3): over Z,
9x^3 - 6x^2 - 56x - 80 = (3x - 10)(3x^2 + 8x + 8). The lifted
subset-reconstruction never finds the (3x-10) divisor, so the
reducible cofactor is emitted as one "irreducible".

## Repro

```
UPoly f = parse("320,-16,-144,-54,27");        // 27x^4-54x^3-144x^2-16x+320
auto fs = factorOverQ(f);
// expected 3 monic factors: x-4/3, x-10/3, x^2+8/3x+8/3
// actual:   2 factors, the cubic x^3-2/3x^2-56/9x-80/9 left unsplit
```

Trace: f mod 5 = 4x(x^2+x+1) — two mod-p factors {x, x^2+x+1}, lifted
to p^5 = 3125. The true integer factor (3x-10) corresponds to the
linear mod-p factor up to a unit, but after lifting, no proper subset
of the lifted factors divides the remaining cofactor exactly, so the
reconstruction falls through to "remaining cofactor is irreducible".
Suspect: the leading-coefficient unit is absorbed into the wrong
mod-p factor (here it must land so that (3x-10) emerges; the current
absorption into the first factor by lcMod does not reproduce the
integer unit split), or the lift converges to the monic representative
of the wrong side.

## Guard

`ZassenhausDebug.QuarticCubicSplitDisabled` (DISABLED_) in
tests/poly/zassenhaus_test.cpp.

Impact: Trager's residue factorization of resultants can return
reducible pieces — residues would still be correct but not minimal,
and the "irreducible c" check would under-approximate. Must be fixed
before the C1 Trager step consumes factorOverQ.
