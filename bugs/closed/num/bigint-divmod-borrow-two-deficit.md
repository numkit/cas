# bigint-divmod-borrow-two-deficit

Kind: bug
Status: ✅ FIXED (dc5224e)
Area: num

## Description

`BigInt::divMod` produced quotients/remainders off by an exact multiple of
2^(32k) (typically 2^128) for some dividends two limbs longer than the
divisor: low digits of the remainder matched, the top was wrong by a
carried unit. Found by 200k-case Python fuzz of the digit-level algorithm;
not reproducible with 4-limb operands alone.

## Repro

```
U = 1122773768074971116050097213187953532848441185054
V = 311976394803616410309083796225284973465
U % V  →  289549606005341838747190216584499984850
   expected 289549605926113676232925878990956034514
(U / V was correct: 3598906156)
```

## Root cause

In the multiply-subtract loop of Knuth algorithm D the per-digit borrow can
reach 2 (deficit `sub - cur` can exceed 2^32, since the running borrow k
goes up to 2^32). An "unsigned-clean" rewrite clamped the borrow to {0, 1}
via `borrow = sub > cur`, silently dropping 2^32. Hacker's Delight
expresses this as `k = (p >> 32) - (t >> 32)` with a signed `t`, where the
arithmetic shift yields borrow ∈ {0, 1, 2}.

## Fix

Compute the exact deficit while the digit is still intact and take
`ceil(deficit / 2^32)` as the borrow:

```
k = (p >> 32) + ((deficit + 0xFFFFFFFF) >> 32)   // deficit > 0
```

Validated by a 500k-case Python fuzz with biased nasty patterns
(small top digits → large s; all-ones digit runs): 0 mismatches.

## Guard

`BigIntProperty.TruncDivisionInvariants` and
`BigIntProperty.AlgebraInvariants` (50k iterations over 1–4-limb operands
with nasty-value injection).
