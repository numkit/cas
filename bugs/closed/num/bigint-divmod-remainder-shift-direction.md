# bigint-divmod-remainder-shift-direction

Kind: bug
Status: ✅ FIXED (dc5224e)
Area: num

## Description

`BigInt::divMod` returned a corrupted remainder whenever the normalization
shift `s = nlz32(v[n-1])` was non-zero. Small corruptions broke
`a == q*b + r`; large ones (r > |b|) made `BigInt::gcd` loop forever —
the original symptom was a hung test process.

## Repro

```
divMod(123456789012345678901234567890, 147824519365982347130729595140281729024)
  → q = 0, r = 170141183544311939477677441783491922642
    expected r = 123456789012345678901234567890
```

Hang reproducer (Euclid never terminates because r ≥ b):

```
gcd("987654321098765432109876543210", "123456789012345678901234567890")
  → infinite loop, expected 9000000000900000000090
```

## Root cause

Denormalization of the remainder (`un >> s`) pulled carry bits from the
digit BELOW (`un[i-1] << (32-s)`) — the formula for a LEFT shift. A right
shift must pull bits from the digit ABOVE: `(un[i] >> s) | (un[i+1] << (32-s))`,
with `r[n-1] = un[n-1] >> s` (Hacker's Delight divmnu). The bug was masked
when `s == 0` (divisor top digit ≥ 2^31), which is why many random
divisions still passed.

## Fix

Rewrote the remainder extraction to shift bits down from `un[i+1]`.

## Guard

`BigIntProperty.TruncDivisionInvariants` (50k randomized divisions assert
`q*b + r == a` and `|r| < |b|`), `BigIntGcd.FixedAndProperties` (the
previously-hanging pair is a fixed case).
