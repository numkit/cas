# diff-null-child-and-sqrt

Kind: bug
Status: ✅ FIXED (b0a0119)
Area: core

## Description

1. `Ctx::diffRec` in `src/core/diff.cpp` does not handle `Func("sqrt", u)`, even though `parseExpr` parses `sqrt(...)` as `Func("sqrt", u)` and `evalDouble` evaluates it.
2. In Release (`NDEBUG`), when `diffRec` returns a null `Expr()` for an unsupported `Func`, parent `Add`, `Mul`, `Pow`, and `Func` branches in `diffRec` do not check `.isNull()` on recursive child derivatives before passing them to `add(...)` / `mul(...)`, causing an out-of-bounds `nodes_[id - 1]` access (`0xc0000005` SEH crash).

## Repro

```cpp
Ctx c;
Expr x = c.symbol("x");
Expr f = parseExpr(c, "sqrt(1 + x)*exp(-x)");
Expr df = c.diff(f, x); // Release: SEH 0xc0000005 in makeMul; Debug: assert in diffRec
```

## Root cause

`diffRec` lacked the `"sqrt"` derivative rule $\frac{d}{dx}\sqrt{u} = \frac{1}{2} u^{-1/2} u'$, and its composite node cases (`Add`, `Mul`, `Pow`, `Func`) assumed recursive `diffRec` calls never return a null `Expr`.

## Fix

1. Add `"sqrt"` support to `Ctx::diffRec` (`1/2 * u^(-1/2) * du`) and `Ctx::evalExact` (`sqrt(0) = 0`, `sqrt(1) = 1`).
2. Guard `Ctx::diff` and all recursive `diffRec` branches against null `Expr` so unsupported functions inside compound expressions cleanly propagate `Expr()` in Release instead of crashing.

## Guard

`DiffTest.SqrtAndNullPropagationInRelease` and `SeriesTest.PropertyDerivativeCommutesWithTaylor`.
