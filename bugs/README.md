# Bug catalog

One file per bug. Lifecycle: `bugs/opened/<area>/` → `bugs/closed/<area>/`
(`git mv` on fix; record the commit hash and the guarding test).

Areas match source layout: `num`, `core`, `poly`, `integrate`, `gate`.

## Template

```markdown
# <short-name>

Kind: bug | crutch | cleanup
Status: OPEN | ✅ FIXED (<commit hash>)
Area: <num|core|poly|integrate|gate>

## Description

What is wrong and where (file / function).

## Repro

Exact, copy-paste-runnable reproduction: inputs, expected vs actual.
Use decimal strings for numeric values so the repro survives API changes.

## Root cause

Why it happens (filled in once known).

## Fix

What changed.

## Guard

GTest name that fails without the fix.
```

## Tags

- `bug` — real defect (wrong result / crash / hang).
- `crutch` — a workaround bridge in the code, marked for removal when its
  underlying defect closes (**Guard:** deferred).
- `cleanup` — legacy / stale / dead code to clean (**Guard:** deferred).
