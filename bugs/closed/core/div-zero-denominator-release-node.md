# div-zero-denominator-release-node

Kind: bug
Status: ✅ FIXED (this change; hash recorded on close)
Area: core

## Description

`Ctx::div(a, b)` with a NUMERIC ZERO `b` builds `Pow(0, -1)` and a
Mul over it. In Debug the assert fires; in Release the assert is
compiled out and the caller receives a LIVE GARBAGE NODE
`0^-1 * a` — a tree that violates the core's own contract (no
0-to-negative-power nodes), prints as such (`1/2*0^-1`), and can
propagate into answers. The same hole exists in `Ctx::pow(0, k)`
for negative integer `k`.

Found by the radical-storey property generator: it built a
denominator `[rr0, rr1, 1] = [-1, 0, 1]` whose canonical sum is an
honest ZERO, and `div` happily produced `1/2 * 0^-1`.

## Repro

```
Ctx c;
Expr x = c.symbol("x");
// Debug: assert fires. Release (NDEBUG): returns a live node.
Expr e = c.div(x, c.zero());      // mul(x, pow(0,-1))
c.toString(e);                    // "0^-1*x"  <- contract-violating node
```

## Root cause

`div` guards the numeric-zero denominator only with `assert`, and
`pow`'s zero-base negative-exponent branch likewise. Release builds
need a defined safe outcome instead of UB-shaped garbage nodes.

## Fix

Release semantics aligned with the existing "null Expr = invalid"
convention (diff already uses it): both paths return a null Expr in
Release; the Debug asserts stay as the early tripwire.

## Guard

`ExprTest.ZeroDenominatorIsNullInRelease` (runs the null checks
under NDEBUG; skipped in Debug where the assert is the contract).
