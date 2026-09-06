# bigint-tostring-chunk-padding

Kind: bug
Status: ✅ FIXED (dc5224e)
Area: num

## Description

`BigInt::toString()` emitted leading zeros when the decimal representation
needed more than one 19-digit chunk: the zero-padding to width 19 was
applied to the TOP chunk instead of every non-top chunk. Found while writing
the founding tests.

## Repro

```
BigInt v = BigInt(1) << 128;
v.toString()
```

Actual: `000000000000000000340282366920938463463374607431768211456`
Expected: `340282366920938463463374607431768211456`

## Root cause

Chunks are produced least-significant first; the code skipped padding for
the first-produced chunk regardless of position. Padding must be applied to
every chunk except the last-produced one (the most significant).

## Fix

Pad the chunk when the next quotient is non-zero (`if (!q.isZero())`).

## Guard

`BigIntShift.BasicsAndFloorSemantics` (exact-string asserts for 2^64 and
2^128), `BigIntProperty.StringRoundTrip` (50k round-trips).
