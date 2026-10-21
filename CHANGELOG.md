# Changelog

## v0.5.0 — 2026-10-21

Echelon 5 release: non-elementary special functions (`erf`, `erfc`, `erfi`,
`Ei`, `li`, `Si`, `Ci`, `FresnelS`, `FresnelC`) across derivatives, exact and
IEEE-754 evaluation, simplification, Taylor/Laurent series, asymptotic limits,
and certified symbolic/definite integration (`core/`, `integrate/ratint`);
symbolic residues `residue(c, f, var, z0)` and contour-integration methods in
`definiteIntegrate` (Cayley–Weierstrass unit-circle transformation, interior
antiderivative branch-jump correction, and Jordan's lemma Fourier integrals);
unilateral Z-transform `ztrans` / `iztrans` and certified linear recurrence
equation solver `rsolve` / `rsolveIVP` (`transform/ztrans`); and canonical
exact matrix decompositions `rref`, `rank`, `lu` ($PA = LU$), `gramSchmidt` /
`qr` ($A = QR$), and Jordan canonical form `jordanForm` ($AP = PJ$)
(`linalg/symmatrix`).

### Highlights & New Capabilities

- **Non-Elementary Special Functions (`core/`, `integrate/ratint`, Item 49)**:
  - Full support for `erf`, `erfc`, `erfi`, `Ei`, `li`, `Si`, `Ci`, `FresnelS`,
    and `FresnelC` across `Ctx::diff`, `Ctx::evalExact`, dependency-free
    `Ctx::evalDouble` (power series, continued fractions, composite 8-point
    Gauss–Legendre quadrature, and large-argument asymptotics), `Ctx::assume`
    sign/reality inference, and `simplify` (parity identities and
    `erf`/`erfc` complement folding).
  - Taylor/Laurent series expansion and asymptotic limits at $\pm\infty$ in
    `core/series` ($\operatorname{erf}(\pm\infty) = \pm 1$,
    $\operatorname{erfc}(+\infty) = 0$, $\operatorname{erfc}(-\infty) = 2$,
    $\operatorname{Si}(\pm\infty) = \pm\pi/2$, $\operatorname{Ci}(+\infty) = 0$,
    $\operatorname{Ei}(-\infty) = 0$,
    $\operatorname{FresnelS}(\pm\infty) = \operatorname{FresnelC}(\pm\infty) = \pm 1/2$).
  - `integrateSpecialFunctions` storey in `integrate/ratint` with polynomial-by-parts
    reduction and symbolic derivative certification $D(F) \equiv f$, unlocking
    Gaussian ($\int_{-\infty}^\infty e^{-ax^2}\,dx = \sqrt{\pi/a}$), Dirichlet
    ($\int_0^\infty \frac{\sin(ax)}{x}\,dx = \frac{\pi}{2}\operatorname{sgn}(a)$),
    and Fresnel ($\int_0^\infty \sin(x^2)\,dx = \int_0^\infty \cos(x^2)\,dx = \frac{1}{2}\sqrt{\pi/2}$)
    improper integrals in `definiteIntegrate`.
- **Symbolic Residues & Contour Integration (`core/series`, `integrate/ratint`, Item 50)**:
  - `residue(Ctx&, f, var, z0, Budget*)` computing residues at finite poles
    (via Laurent coefficient $(z - z_0)^{-1}$ with high-order pole derivative
    fallback for symbolic poles) and at $\infty$ via $-\operatorname{Res}_{t=0}(t^{-2}f(1/t))$.
    Exposed in CLI as `nkcas residue`.
  - Unit-circle / Cayley–Weierstrass contour transformation for rational
    trigonometric integrals $R(\cos x, \sin x)$ over $[a, a + 2k\pi]$ and
    $[0, \pi]$; automatic interior branch-jump correction
    $\sum_{r \in (a,b)} (\lim_{x \to r^-} F(x) - \lim_{x \to r^+} F(x))$ for
    antiderivatives with interior $\arctan$ discontinuities; and Jordan's lemma
    upper-half-plane residue calculus for Fourier integrals
    $\int_{-\infty}^\infty R(x)\cos(\omega x)\,dx$ and
    $\int_{-\infty}^\infty R(x)\sin(\omega x)\,dx$.
- **Unilateral Z-Transform & Certified Recurrence Solver (`transform/ztrans`, Item 51)**:
  - `ztrans(Ctx&, f, n, z, Budget*)` and `iztrans(Ctx&, F, z, n, Budget*)`:
    forward unilateral Z-transform (geometric/exponential sequences, shift-derivative
    operator $(-z\frac{d}{dz})^k$, discrete impulse `kroneckerDelta(n - k)`,
    damped trig/hyperbolic sequences) and partial-fraction inverse over
    $\mathbb{Q}[z]$ (repeated rational poles via binomial basis
    $\binom{n}{k-1}r^{n-(k-1)}$, real-radical quadratic poles such as Binet's
    Fibonacci formula, and complex-conjugate oscillatory poles), certified by
    round-trip $\mathcal{Z}\{\mathcal{Z}^{-1}\{F\}\}(z) = F(z)$. Exposed in CLI
    as `nkcas ztrans` and `nkcas iztrans`.
  - `rsolve` and `rsolveIVP` solving $K$-th order constant-coefficient linear
    recurrence equations $\sum_{k=0}^K a_k y(n+k) = \text{rhs}(n)$ with symbolic
    recurrence and initial-value certification.
- **Canonical Exact Matrix Decompositions (`linalg/symmatrix`, Item 52)**:
  - `rref(Ctx&, A, pivotColsOut, Budget*)` and `rank(Ctx&, A, Budget*)`.
  - `lu(Ctx&, A, Budget*)` (`LUDecomposition` with $P A = L U$, permutation
    vector `perm`, sign `sign`, and symbolic certificate $PA - LU = 0$).
  - `gramSchmidt(Ctx&, cols, normalize, Budget*)` and `qr(Ctx&, A, Budget*)`
    (`QRDecomposition` with rational unnormalized projections and symbolic
    certificates $QR = A$ and $Q^T Q = I_n$).
  - `jordanForm(Ctx&, A, Budget*)` (`JordanDecomposition` with nilpotent-power
    cycle extraction supporting arbitrary Jordan block partitions per eigenvalue,
    certified by $AP = PJ$ and $P P^{-1} = I_n$).

---

## v0.4.0 — 2026-10-21

Echelon 4 release: proper and improper definite integration
`definiteIntegrate` with one-sided and infinite limits `limitOneSided` /
`limitAtInfinity` and special-angle trigonometry (`integrate/ratint`,
`core/series`, `core/simplify`), symbol domain assumptions `AssumeDomain`
with recursive DAG sign/reality/integrality inference (`core/expr`,
`core/simplify`, `rubi/rules`), forward and certified inverse unilateral
Laplace transforms `laplace` / `ilaplace` (`transform/laplace`), and exact
matrix nullspace, symbolic eigenvalues/eigenvectors, certified matrix
exponential `matrixExp`, and 1st-order linear ODE systems solver
`dsolveSystem1Linear` / `dsolveSystem1LinearIVP` (`linalg/symmatrix`,
`ode/dsolve`).

### Highlights & New Capabilities

- **Definite & Improper Integration and Infinite Limits (`integrate/ratint`, `core/series`, Item 44)**:
  - `definiteIntegrate(Ctx&, f, var, a, b, Budget*)` (`DefiniteIntegral` with
    `ProvedSymbolic`, `Divergent`, and `Unevaluated` verdicts): applies
    Newton–Leibniz and one-sided/infinite endpoint limits, detects interior
    poles on $(\min(a,b), \max(a,b))$ via `solveRealRoots` + `refineRoot`
    while filtering out removable singularities, and realizes the real
    $\log|u|$ branch at negative endpoints. Exposed in CLI as `nkcas defint`.
  - `limitOneSided` (with automatic Puiseux $x = x_0 \pm t^2$ square-root
    branch-point fallback) and `limitAtInfinity` (plus symbolic `inf`/`oo`/
    `infinity` and `-inf` support in `limit`), full asymptotic Laurent expansion
    of $\arctan(u)$ and $\operatorname{acot}(u)$ as $u \to \pm\infty$,
    exponential decay $\exp(u) \to 0$, logarithm combination for $\infty - \infty$,
    and bounded-oscillation squeeze in `core/series`.
  - Exact evaluation of `sin`/`cos`/`tan`/`cot`/`sec`/`csc` at rational
    multiples of $\pi$ with denominators $q \in \{1,2,3,4,6\}$ and special
    values of `asin`/`acos`/`atan`/`acot` in `core/simplify`.
- **Symbol Assumptions & Recursive DAG Inference (`core/expr`, `core/simplify`, `rubi/rules`, Item 45)**:
  - `AssumeDomain` (`Any`, `Real`, `Positive`, `Negative`, `NonNegative`,
    `Integer`), `Ctx::assume`, `Ctx::assumption`, `Ctx::clearAssumptions`, and
    recursive DAG predicates `isAssumedPositive`, `isAssumedNegative`,
    `isAssumedNonNegative`, `isAssumedReal`, and `isAssumedInteger`.
  - Assumption-aware simplification in `core/simplify` ($\sqrt{u^2} \to \pm u$,
    radical factor extraction $\sqrt{4 u^2 y} \to \pm 2 u \sqrt{y}$,
    $(u^a)^b \to u^{ab}$, $\log(u^p) \to p\log u$, $|u| \to \pm u$,
    $\operatorname{asinh}(\sinh x) \to x$, $\sin(n\pi) \to 0$,
    $\cos(n\pi) \to (-1)^n$) and symbolic parameter support in Rubi predicates
    (`PosQ`/`NegQ`/`GtQ`/`LtQ`/`GeQ`/`LeQ`/`IntegerQ`/`IntegersQ` and `Rt`).
- **Forward & Certified Inverse Laplace Transforms (`transform/laplace`, Item 46)**:
  - `laplace(Ctx&, f, t, s, Budget*)`: unilateral Laplace transform supporting
    linearity, integer and half-integer powers $t^n$ and $t^{k/2}$ via exact
    $\Gamma(n + 1/2) = \frac{(2n-1)!!}{2^n}\sqrt{\pi}$, exponentials,
    phase-shifted trigonometric and hyperbolic functions, frequency shift
    $e^{at}g(t) \implies G(s-a)$, frequency differentiation
    $t^n g(t) \implies (-1)^n G^{(n)}(s)$, and trig/hyperbolic product-to-sum
    reduction.
  - `ilaplace(Ctx&, F, s, t, Budget*)`: inverse Laplace transform via
    Zassenhaus factorization `factorOverQ` and partial-fraction decomposition
    over $\mathbb{Q}[s]$ (repeated real poles, repeated complex-conjugate
    quadratic poles via completion of the square and shift recurrence,
    real-radical quadratic poles, and parametric forms), certified by checking
    $\mathcal{L}\{\mathcal{L}^{-1}\{F\}\}(s) = F(s)$. Exposed in CLI as
    `nkcas laplace` and `nkcas ilaplace`.
- **Spectral Linear Algebra, Matrix Exponential & 1st-Order Linear ODE Systems (`linalg/symmatrix`, `ode/dsolve`, Item 47)**:
  - `nullspace(Ctx&, A, Budget*)` via Gauss–Jordan RREF with cross-multiplied
    pivot elimination; `EigenPair`, `eigenvalues`, and `eigenvectors` via
    `charpoly` + `factorOverQ` / `solveSymbolic`; and certified
    `matrixExp(Ctx&, A, t, Budget*)` ($e^{At}$) via Laplace resolvent inversion
    $\mathcal{L}^{-1}\{(sI - A)^{-1}\}(t)$, $2 \times 2$ Putzer /
    Cayley–Hamilton closed form, and generalized Jordan chains.
  - `dsolveSystem1Linear` and `dsolveSystem1LinearIVP` solving homogeneous and
    inhomogeneous systems $\mathbf{y}'(x) = A\mathbf{y}(x) + \mathbf{f}(x)$
    across distinct real, repeated/defective Jordan blocks, and
    complex-conjugate eigenvalues $\alpha \pm i\omega \implies e^{\alpha x}\cos/\sin(\omega x)$,
    with Variation of Parameters $\Phi(x)\int\Phi(-x)\mathbf{f}(x)\,dx$ and
    componentwise ODE + initial-condition certification.

---

## v0.3.0 — 2026-10-21

Echelon 3 release: cost-guided algebraic/trigonometric/hyperbolic/logarithmic
`simplify` engine (`core/simplify`), Rubi R3–R5 scaling to 60 rule files and
2058 elementary rules across trinomials, exponentials, logarithms,
trigonometry, inverse trig, and hyperbolics (`rubi/`), exact symbolic
equation & 2-variable polynomial system solver `solveSymbolic` /
`solveSystem2` (`core/symsolve`), and certified 1st- and 2nd-order ordinary
differential equation solver `dsolve` (`ode/dsolve`).

### Highlights & New Capabilities

- **Cost-Guided Expression Simplification (`core/simplify`, Item 39)**:
  - `simplify(Ctx&, Expr)` and `Ctx::simplify(Expr)` minimize the
    lexicographic cost pair `(Ctx::exprCost, Ctx::leafCount)` across
    bottom-up structural rewrites, `expand`, rational GCD reduction
    `simplifyRationalExpr`, polynomial factorization `factorExpr`,
    Pythagorean and hyperbolic identities ($A\sin^2 u + A\cos^2 u \to A$,
    $C - C\sin^2 u \to C\cos^2 u$, $A\cosh^2 u - A\sinh^2 u \to A$,
    double-angle formulas), inverse function compositions
    ($\exp(\log u) \to u$, $\log(\exp u) \to u$, $\sin(\arcsin u) \to u$,
    $\cos(\arcsin u) \to \sqrt{1-u^2}$, etc.), `tan/cot/sec/csc` to
    `sin/cos` conversions, and logarithmic/power rules. Exposed in CLI as
    `nkcas simplify`.
- **Rubi R3–R5 Transcendental & Trinomial Scaling (`rubi/`, Item 40)**:
  - Expanded `third_party/rubi-snapshot/` to **60 `.m` rule files**
    (**2058 elementary rules**, 10301 discrimination-tree nodes in
    `src/rubi/rubi_tables_1111.inc`) covering `1.1` binomials, `1.2`
    quadratic & quartic trinomials, `2` exponentials, `3` logarithms, `4`
    trigonometry, `5` inverse trigonometry, `6` hyperbolics, and `7`
    inverse hyperbolics.
  - Added derivatives for `cot`, `sec`, `csc`, `acot`, `coth`, `sech`,
    `csch` in `src/core/diff.cpp`, and integrated `checkSimplifiedDelta`
    (`rewriteTrigToSinCos`, `clearNestedDenominators`, and common-denominator
    clearance) into `certificateHolds` in `src/rubi/rules.cpp`.
  - Expanded `corpora/rubi-slice.txt` to **600 tasks** across 24 R1–R5
    families with **100% pass rate** and $\text{MLR} = 1.00$.
- **Symbolic Equation & System Solver (`core/symsolve`, Item 41)**:
  - `solveSymbolic(Ctx&, Expr eqn, Expr var, Budget*)`: solves factored
    products, single-occurrence transcendental/power equations by inverse
    peeling, rational polynomials via Zassenhaus factorization (`factorOverQ`,
    emitting exact rationals, radicals, and `RootOf` atoms), and parametric
    symbolic polynomials of degree $\le 4$ (linear, quadratic with exact
    square extraction, binomial, and biquadratic), filtering out pole roots.
  - `solveSystem2(Ctx&, Expr eq1, Expr eq2, Expr x, Expr y, Budget*)`:
    solves 2-variable polynomial systems via the Sylvester resultant
    determinant in `SymMatrix`, certifying every $(x_i, y_j)$ solution pair
    by substitution into both equations. Exposed in CLI as `nkcas symsolve`.
- **Certified 1st- and 2nd-Order ODE Solver (`ode/dsolve`, Item 42)**:
  - `dsolve1` / `dsolve1IVP`: solves 1st-order quadrature, linear
    $y' = A(x)y + B(x)$ (via integrating factor and undetermined
    coefficients), separable $y' = g(x)h(y)$, and Bernoulli
    $y' = A(x)y + B(x)y^n$ ODEs and initial value problems.
  - `dsolve2Linear` / `dsolve2LinearIVP`: solves 2nd-order constant-coefficient
    linear ODEs $a y'' + b y' + d y = f(x)$ across overdamped ($\Delta > 0$),
    critically damped ($\Delta = 0$), and underdamped oscillatory
    ($\Delta < 0 \to e^{\alpha x}\cos/\sin$) regimes, finding particular
    solutions via differential-closure undetermined coefficients (`SymMatrix` +
    `linsolve` with automatic resonance multiplicity shift) and variation of
    parameters via the Wronskian. Every ODE solution is certified by
    substitution into the differential equation. Exposed in CLI as
    `nkcas dsolve`.

### Metrics (plan section 7; Release build at tag time)

| corpus                | tasks | pass | verification | MLR  | median  | p95     |
|-----------------------|-------|------|--------------|------|---------|---------|
| rational-baseline     | 500   | 100% | 100%         | —    | 9.37 ms | 54.7 ms |
| rubi-slice (R1–R5)    | 600   | 100% | 100%         | 1.00 | 91 µs   | 816 µs  |

All section-7 targets met: fast-path median 91 µs (target ≤ 500 µs),
heavy-path median 9.37 ms (target ≤ 50 ms), Mean Leaf Ratio **1.00** over
all 600 Rubi R1–R5 reference tasks (target ≤ 1.00), full 236-test Release
suite finishes in **27.5 s**.

---

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
