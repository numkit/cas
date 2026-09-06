# ratint-pfd-stale-cofactor

Kind: bug
Status: ✅ FIXED (3590939)
Area: integrate

## Description

The iterative partial-fraction decomposition in `integrate/ratint.cpp`
computed the extraction cofactor for modulus P_i as the product of ALL
other moduli — including the ones already stripped in earlier
iterations. The running remainder at step i lives over the product of
the REMAINING moduli only, so the stale factor corrupted every Bi after
the first: wrong residues (off by the stripped factors' values) and a
failed Tier-1 certificate.

## Repro

```
den = ((x + 4) * (x + 1) * (x^2 + 3x + 9/2))^2
num = 1 + 5x
integrateRational(num/den)
```

Actual: `Unevaluated, "internal certificate check failed"` — the log
coefficient at (x + 4) came out as +6124/397953 instead of the true
residue -306200/6632550 (exactly the true value divided by -3, the
value of the already-stripped (x + 1) at x = -4).
Expected: `ProvedSymbolic` with logs, a rational part and an atan.

The Hermite reduction path was NOT affected: it calls the PFD with a
single modulus, which takes the trivial last-element branch — which is
why the Hermite property tests passed while full integration failed.

## Root cause

Cofactor confusion between the one-shot PFD identity
(Bi = N * inv(D/Pi) mod Pi over the full product D) and the iterative
residual form (remainder over the shrinking product).

## Fix

Compute the cofactor as the product of the moduli after idx:
`for j in idx+1..k: prod *= Ps[j]`.

## Guard

`RatIntTest.FullIntegrationDoD` — 2000 random products of linear and
square-discriminant quadratic factors with multiplicities 1..3, every
integration must return PROVED_SYMBOLIC. The certificate check inside
`integrateRational` is itself the tripwire that refused to certify the
wrong residues (the bug never produced a wrong answer, only an honest
Unevaluated).
