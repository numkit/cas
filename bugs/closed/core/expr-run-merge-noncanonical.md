# expr-run-merge-noncanonical

Kind: bug
Status: ✅ FIXED (b227998)
Area: core

## Description

The first implementation of `Ctx::makeAdd`/`makeMul` merged only runs of
*identical* children (x + x → 2*x, x · x → x^2). That is not a
canonicalization: the result depends on how the input is grouped, and a
canonical node could end up containing the same child twice. Caught by the
`CloneRebuildIsIdentical` property test (rebuild of a canonical tree
produced a DIFFERENT tree), not by any fixed-vector test.

## Repro

```
Ctx c;
Expr y = c.symbol("y");
c.toString(c.add({y, y, c.mul({c.number(2), y)}))
```

Actual: `2*y + 2*y` — an Add whose child array contains the SAME node
(`Mul[2,y]`) twice: the run of two y's folded into `Mul[2,y]`, which then
coexists with the original `Mul[2,y]` child.
Expected: `4*y`.

Mul mirror: `mul({x, x, pow(x, 2)})` → `x^2*x^2` instead of `x^4`.

Any rebuild through the API "fixes" the tree, so equality-by-id and
clone/rebuild diverge — fatal for a hash-consed DAG.

## Root cause

Run merging is syntactic; it does not account for children already in
coefficient/exponent form. `y + y + 2*y` has runs `[y, y]` and `[Mul[2,y]]`
which fold independently into two copies of `Mul[2,y]`.

## Fix

Coefficient-aware like-term collection. `makeAdd` decomposes every
non-number child into (coefficient, term) — a canonical Mul carries its
numeric constant as the first child — and sums coefficients of equal
terms; `makeMul` symmetrically decomposes into (base, exponent) and sums
exponents (rational sums included: x^(1/2)·x^(1/2) → x). Zero
coefficients/exponents drop terms (x + (-x) → 0, x·x^-1 → 1).

## Guard

`RandomExprTest.CloneRebuildIsIdentical` (the test that caught it),
`RandomExprTest.RepeatedBuildIsIdentical`, regression cases in
`ExprTest.AddCanonicalFolding` / `ExprTest.MulCanonicalFolding`
(`y + y + 2*y → 4*y`, `x·x·x^2 → x^4`), plus a debug-only
no-duplicate-children assert in makeAdd/makeMul.
