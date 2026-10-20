# rubi-pattern-canon-and-nonlinear-bind

Kind: bug
Status: ✅ FIXED (HEAD — Stage R1a)
Area: integrate

## Description

Three latent defects in the Rubi pattern compiler (`tools/rubi_codegen.py`)
and runtime matcher/executor (`src/rubi/rules.cpp`) prevented rules already
present in `src/rubi/rubi_tables_1111.inc` from matching or terminating cleanly:

1. **Un-canonicalized pattern operators/heads in `rewrite_div`
   (`tools/rubi_codegen.py`)**: `rewrite_div` rewrote `1/d -> d^-1` and
   `a/b -> a*b^-1`, but left `Sqrt[u]`, `neg[num]`, `/[num, num]`, and nested
   integer powers `^[Sqrt[u], -1]` un-canonicalized. Because `Ctx` represents
   square roots as `Pow(u, 1/2)`, negative rational exponents as single
   `NodeKind::Number` values (e.g. `-3/2`), and folds `(u^(1/2))^-1 -> u^(-1/2)`,
   60 of the 78 committed rules (including `1/Sqrt[a + b*x^2]` and
   `1/(a + b*x^2)^(3/2)`) were unreachable dead trie branches.
2. **Unchecked non-linear pattern variables and single-shot leaf commitment in
   `src/rubi/rules.cpp`**: `matchAt` pushed `Binding{vName, e}` unconditionally
   without checking whether `vName` was already bound in `acc`. Consequently,
   non-linear patterns such as `(a_. + b_.*x_)^m_*(c_ + d_.*x_)^m_` matched
   products with distinct exponents (`m = 2` and `m = 3`), and once `matchAt`
   committed to a leaf whose rule chain declined, it returned `false` without
   backtracking to less specific trie branches.
3. **Unbounded `Int[...]` recursion on self-calls and fallback cycles in
   `src/rubi/rules.cpp`**: When an upstream rule's primary leaf declined (for
   example `(1 + x^2)^(1/4)` declining `EllipticE`), fallback normalization rules
   such as `1.1.2.1` line 148 (`Int[1/(a+b*x^2)^(1/4), x] -> Int[1/(1+b*x^2/a)^(1/4), x]`
   at `a = 1`) or `1.1.1.2` two-step shift cycles (`(-1/2, -1/2) <-> (1/2, -3/2)`)
   recursed without bound.

## Repro

1. Pattern canonicalization:
   - Input: `rubiApply(t, c, parseExpr(c, "(1 + x^2)^(-1/2)"), x)`
   - Expected: `"asinh(x)"`
   - Actual (before fix): null `Expr` (trie edge `HEAD Sqrt` under `^ [..., -1]`
     never matched canonical `^ [1 + x^2, -1/2]`).
2. Non-linear pattern variable binding:
   - Input: `matchFirst(t, c, parseExpr(c, "(1 + x)^2*(1 - x)^3"), b)`
   - Expected: matches `(a_. + b_.*x_)^m_*(c_. + d_.*x_)^n_` with `m = 2, n = 3`.
   - Actual (before fix): matched `(a_. + b_.*x_)^m_*(c_ + d_.*x_)^m_` with
     duplicate bindings `{m: 2, m: 3}`.
3. Self-recursion on elliptic-only fractional power:
   - Input: `rubiApply(t, c, parseExpr(c, "(1 + x^2)^(1/4)"), x)`
   - Expected: null `Expr` (honest decline).
   - Actual (before fix): stack overflow via `a = 1` self-call in `1.1.2.1`.

## Root cause

- `tools/rubi_codegen.py`: `rewrite_div` only handled top-level `/` and did not
  fold `neg[num]`, `/[num, num]`, `Sqrt[u] -> ^[u, 1/2]`, or `(u^r)^n -> u^(r*n)`.
- `src/rubi/rules.cpp`: `matchAt` mutated `acc` in-place along a single greedy
  path without checking `findBinding(acc, vName)` and without a pending-work
  stack capable of backtracking across sibling trie edges and leaf chains.
- `src/rubi/rules.cpp`: `buildReplacement` (`head == "Int"`) invoked `rubiApply`
  with neither a self-call check (`integrand == currentE`) nor a recursion depth
  cap.

## Fix

- Extended `rewrite_div` and added `make_pow` in `tools/rubi_codegen.py` to
  canonicalize `neg[num]`, `/[num, num]`, `Sqrt[u]`, and `(u^r)^n`; regenerated
  `src/rubi/rubi_tables_1111.inc` (trie nodes reduced from 177 to 129 as split
  duplicate paths merged).
- Replaced `matchAt` in `src/rubi/rules.cpp` with backtracking `matchStep` over
  an explicit pending-expression stack `work`, enforcing equality on already-bound
  pattern variables (`findBinding`), prioritizing bound wildcards over fresh
  wildcards, supporting binary `Mul` commutativity, and backtracking when an
  entire leaf chain declines.
- Added self-call rejection (`integrand == currentE && iVar == var`) and bounded
  recursion depth (`kMaxRubiDepth = 8`) in `rubiApplyDepth`.

## Guard

- `RubiMatcher.NonlinearPatternRequiresEqualBindings`
- `RubiApply.R1aInverseTrigAndHyperbolic`
- `RubiApply.R1aFractionalAndNegativePowers`
- `RubiApply.PropertyR1aShapes`
