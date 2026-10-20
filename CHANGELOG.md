# Changelog

## v0.2.0 — 2026-10-20

Symbolic Math Toolbox core release: full Rubi `1.1 Binomial products`
coverage (1365 rules), Mean Leaf Ratio quality gate ($\text{MLR} = 1.00$),
unified `integrate` cascade with `Budget` tracking, 128-bit `BigInt`
Small Buffer Optimization, numeric evaluation (`toDouble` / `evalDouble`),
truncated Taylor/Laurent series and symbolic `limit`, and symbolic
linear algebra (`SymMatrix`: `jacobian`, `gradient`, `hessian`, `det`,
`inv`, `linsolve`, `charpoly`).

### Highlights & New Capabilities

- **Full Rubi `1.1 Binomial products` section (`rubi/`, Item 32)**:
  - Compiled all 33 active upstream `.m` rule files across `1.1.1 Linear`
    (7 files), `1.1.2 Quadratic` (14 files), `1.1.3 General` (8 files),
    and `1.1.4 Improper` (4 files) into `src/rubi/rubi_tables_1111.inc`
    (**1365 rules**, 6365 discrimination-tree nodes).
  - Pattern canonicalization in `tools/rubi_codegen.py` (`rewrite_div`,
    `flatten_mul`, `spec_norm`), backtracking nonlinear binder with
    `Orderless` binary-to-quaternary `Mul` permutations and optional
    parameter synthesis (`a := 0`, `m := 1`) in `src/rubi/rules.cpp`.
  - Runtime support for `With`, `Module`, `Subst`, `ReplaceAll`,
    `SubstFor`, `ExpandIntegrand`, `ExpandToSum`, `Coeff`, `Expon`,
    `PolynomialQuotient`, `PolynomialRemainder`, `Numer`, `Denom`,
    `LinearQ`, `PolyQ`, `IntBinomialQ`, and exact rational root
    extraction in `Rt`/`Sqrt`, plus linear radical substitution
    verification in `certificateHolds`.
- **Form Quality & Mean Leaf Ratio (`core/`, `apps/`, Item 33)**:
  - `Ctx::leafCount(Expr)` (Mathematica/Rubi tree leaf count) and
    `Ctx::exprCost(Expr)` (§6 DAG complexity functional).
  - 5-column corpus runner format (`id<TAB>var<TAB>op<TAB>expr<TAB>ref`)
    computing per-task leaf ratios and corpus-wide Mean Leaf Ratio.
- **Unified `integrate` Cascade & `Budget` Plumbing (`integrate/`, `core/`, Item 34)**:
  - `integrate(Ctx&, Expr f, Expr var, Budget*)`: tries the Rubi fast
    path first, falls back to `integrateRational` (Hermite + Rothstein–Trager +
    Rioboo + Liouvillian storeys), and decomposes `var`-free `Mul`
    factors and mixed `Add` sums termwise under the same proof gate.
  - Extended `Budget` with `BudgetStatus::{Ok, StepExhausted, ArenaExhausted}`
    threaded across Zassenhaus factorization, rational/Liouvillian
    integration, Rubi, series, and linear algebra.
- **128-bit `BigInt` SBO & Numeric Evaluation (`num/`, `core/`, Item 35)**:
  - `BigInt::LimbVec` stores up to 2 limbs (128 bits) inline on the
    stack without heap allocation, paired with single-limb hardware
    `uint64_t` fast paths in `BigInt::divMod` and `BigInt::gcd`.
  - Round-to-nearest-even `BigInt::toDouble()`, scale-invariant 0.5-ULP
    `Rational::toDouble()`, and DAG-memoized `Ctx::evalDouble()`
    (evaluating `Number`, `Symbol` + `pi`/`e`, 56-bit Sturm-refined
    `RootOf` atoms, odd real roots of negatives, elementary functions,
    and `erf`/`erfc`/`gamma`), exposed in CLI as `nkcas eval`.
- **Truncated Taylor/Laurent Series & Symbolic Limits (`core/series`, Item 36)**:
  - `taylor(c, f, var, x0, order)` and `laurent(c, f, var, x0, order)`
    using truncated Laurent series algebra in $t = \text{var} - x_0$ with
    explicit valuation and cancellation accuracy tracking (`maxDeg`),
    binomial fractional powers, differential-integration composition for
    inverse trig/hyperbolic functions, and iterated differentiation
    fallback.
  - `limit(c, f, var, x0)` resolving $0/0$ and $\infty - \infty$ pole
    cancellations via Laurent series, $0 \cdot \log(0)$ rewrites, and
    bounded L'Hopital's rule (`Proved`, `Divergent` with exact
    `poleOrder`, or `Unevaluated`).
- **Symbolic Matrices & Multivariable Calculus (`linalg/symmatrix`, Item 37)**:
  - `SymMatrix` over `Expr` with `simplifyRationalExpr` (common-denominator
    normalization + univariate polynomial GCD cancellation in $\mathbb{Q}(x)$).
  - Vector calculus operators: `jacobian`, `gradient`, `hessian`.
  - Division-free Faddeev–LeVerrier recurrence for `charpoly`,
    `adjugate`, `det`, and `inv`, plus exact linear solver `linsolve`
    (adjugate polynomial fast path for square systems + exact Gaussian
    elimination for rectangular/overdetermined systems).

### Metrics (plan section 7; Release build at tag time)

| corpus             | tasks | pass | verification | MLR  | median  | p95     |
|--------------------|-------|------|--------------|------|---------|---------|
| rational-baseline  | 500   | 100% | 100%         | —    | 9.89 ms | 57.1 ms |
| rubi-slice (1.1.x) | 500   | 100% | 100%         | 1.00 | 47 µs   | 555 µs  |

All section-7 targets met with wide margin: fast-path median 47 µs
(target ≤ 500 µs), heavy-path median 9.89 ms (target ≤ 50 ms; **3.67×
faster** than v0.1.0), Mean Leaf Ratio **1.00** over all 500 Rubi
reference tasks (target ≤ 1.00), full 212-test Release suite finishes in
**29.3 s** (**4× faster** than v0.1.0).

---

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
