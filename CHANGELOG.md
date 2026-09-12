# Changelog

## v0.1.0 — 2026-09-12

First working release: the standalone certified integrator core.
The contract of this release: every integral of the declared class
below is PROVED — a machine-checkable Tier-1 polynomial certificate
plus a Tier-2a certified interval audit of the FORM at runtime — or
an honest `Unevaluated`. Never a wrong answer.

### Declared class (indefinite integrals)

- Rational functions R(x): Hermite reduction + Trager residues;
  quadratic and cubic (Rioboo phase A) algebraic residues emitted
  as real atan/log forms (RootOf atoms where unavoidable).
- Liouvillian storeys: R(e^x), R(log x)/x, R(sin x, cos x) via
  t = tan(x/2), R(x^(p/q)) via t = x^(1/L).
- Rubi fast path: slices 1.1.1.1 (a+b x)^m, 1.1.1.2 (a+b x)^m
  (c+d x)^n, 1.1.2.1 (a+b x^2)^p — 78 upstream rules with recursive
  Int cascades, sign-variant chains, and mirrors of Rubi's 9.1
  utility-tier identities (constant, constant factor, IntSum).
- Operations alongside integration: diff, subs, expand,
  factor (rational functions), solve (exact real polynomial
  roots), parse/print, evalExact (exact rational evaluation).

### Metrics (plan section 7; fresh at tag time, Release build)

| corpus             | tasks | pass | verification | median | p95     |
|--------------------|-------|------|--------------|--------|---------|
| rational-baseline  | 500   | 100% | 100%         | 36.3 ms | 129 ms |
| rubi-slice         | 120   | 100% | 100%         | 76 µs   | 1.21 ms |

Fast-path target (median ≤ 500 µs): met. Heavy path target
(median ≤ 50 ms): met; p95 recorded as the baseline for future
optimization work.

### Known incompleteness (honest Unevaluated — never wrong answers)

- Trager path: denominators with SEVERAL irreducible factors of
  degree ≥ 3 at once (Norm subtraction unimplemented); Rioboo
  beyond cubic fields.
- Rubi fast path: rules whose substitutions need ExpandIntegrand,
  Subst, With-bindings or Sum decline (staged coverage plan R1–R6
  in `notes/c1-algebraic-layer.md`); bare linear monomials x, c·x
  (the matcher requires a Pow node for `x_^m_.`).
- Elliptic/special-function answers and sign assumptions on
  symbolic parameters are outside the certified fragment until the
  holonomic layer (C4) and the provable-assume fragment (S2).
- Definite integrals, limits, series, general simplification,
  complex roots in solve: out of scope for v0.1.0.

### Engineering

- C++17 strict, zero external dependencies in library code (gtest
  is test-only via FetchContent), MSVC-portable (Release + Debug),
  single-threaded base, WASM-safe, PMR-compatible.
- 178 tests green in Release (~119 s); three-layer testing (fixed
  Python-oracle vectors, 50k-iteration property tests, boundary
  tests); Debug targeted gates green, including the full RatIntTest
  suite with active asserts.
- `tools/vendor_sync.py --dry-run` green: the tree reproduces a
  self-contained vendored build — Numkit integration awaits the
  user's explicit command by design.

Reasoning archive (Russian): `notes/`. Roadmap and the v0.2+
version ladder: `notes/first-working-version.md`.
