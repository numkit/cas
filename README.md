# numkit-cas

Symbolic computation core for [Numkit](https://github.com/hotredman/numkit):
exact arithmetic, hash-consed expression DAG, symbolic integration with
proof-carrying verification.

Pure C++17, zero external dependencies (WASM-safe, PMR-compatible memory).
Designed to be vendored into the Numkit tree as the `symbolic` toolbox core;
integration constraints (C++17, no deps, single-threaded base, PMR) are
binding for all code in this repository.

**Current release: v0.3.0** — the standalone certified symbolic
computation & integration toolbox core. Declared class, corpus metrics
and changelog: `CHANGELOG.md`.

Specification: `notes/cas-integrator-plan.md` (v0.4).

## Layout

```
include/numkit/cas/...   public headers
src/...                  implementation (one .cpp per header)
apps/                    nkcas CLI + section-7 corpus runner
corpora/                 benchmark corpora (rational-baseline, rubi-slice)
tests/...                gtest suite (nkcas_gtest)
tools/, scripts/         offline build tooling (Rubi parser/codegen,
                         corpus generators, vendor sync)
third_party/rubi-snapshot/  upstream Rubi rule files (MIT)
```

## Build & test

```
cmake -S . -B build/msvc -G "Visual Studio 17 2022" -A x64
cmake --build build/msvc --config Release
ctest --test-dir build/msvc -C Release --output-on-failure
```

## CLI

```
build/msvc/apps/Release/nkcas.exe integrate "(expr)" x   # unified certified cascade
build/msvc/apps/Release/nkcas.exe defint "(expr)" x a b  # certified definite / improper integral
build/msvc/apps/Release/nkcas.exe rubi "(expr)" x        # Rubi fast path only
build/msvc/apps/Release/nkcas.exe diff "(expr)" x
build/msvc/apps/Release/nkcas.exe taylor "(expr)" x [x0] [order]
build/msvc/apps/Release/nkcas.exe limit "(expr)" x [x0]  # finite or inf / -inf
build/msvc/apps/Release/nkcas.exe simplify "(expr)"      # cost-guided simplification
build/msvc/apps/Release/nkcas.exe symsolve "(eqn)" x     # symbolic equation solver
build/msvc/apps/Release/nkcas.exe dsolve "(rhs)" x       # certified 1st-order ODE solver
build/msvc/apps/Release/nkcas.exe laplace "(expr)" [t] [s]   # forward Laplace transform
build/msvc/apps/Release/nkcas.exe ilaplace "(expr)" [s] [t]  # certified inverse Laplace transform
build/msvc/apps/Release/nkcas.exe eval "(expr)" [x val]  # IEEE-754 double evaluation
build/msvc/apps/Release/nkcas.exe solve "x^2-2" x        # exact real roots
build/msvc/apps/Release/nkcas.exe expand|factor|subs "(expr)" ...
build/msvc/apps/Release/nkcas.exe corpus corpora/rubi-slice.txt
```

`integrate` prints the antiderivative plus its certificate verdict
(`PROVED_SYMBOLIC` / `PROVED_NUMERIC`); a failed verification is an
honest `UNEVALUATED`, never a silent wrong answer. `corpus` runs a
`id<TAB>var<TAB>[op<TAB>]expr` file and reports the section-7
metrics: pass rate, verification rate, median and p95 time.

## API surface (by layer)

All types live in `numkit::cas`. One `Ctx` owns the interned
expression arena; `Expr` handles are meaningful only inside their
`Ctx`.

**Exact numbers** (`num/`): `BigInt` — arbitrary-precision integers
with 2-limb (128-bit) Small Buffer Optimization, Miller-Rabin `isPrime`,
Pollard-Brent `factorize`, and 0.5-ULP `toDouble()`; `Rational` —
canonical exact rationals, `fromDoubleBits(double)` converts any
finite IEEE double losslessly, and scale-invariant `toDouble()`
rounds to nearest-even without intermediate overflow.

**Expressions & Series** (`core/`): `Ctx::symbol/number/add/mul/pow/func/
neg/div/rootOf` build a canonical hash-consed DAG (structural
equality is pointer identity); `parseExpr(Ctx&, src)` parses
MATLAB-precedence text; `toString` prints round-trip-exact forms;
`diff` differentiates elementary and inverse trig/hyperbolic functions;
`subs` substitutes subtrees; `expand` distributes to polynomial form;
`evalExact` evaluates exactly in Q with honest declines outside;
`evalDouble` evaluates DAGs (including Sturm-refined `RootOf` atoms and
special functions `erf`/`erfc`/`gamma`) to `double`; `leafCount` and `exprCost` measure expression size and DAG complexity;
`AssumeDomain` and `Ctx::assume` attach domain assumptions (`Real`,
`Positive`, `Negative`, `NonNegative`, `Integer`) with DAG-level sign,
reality, and integrality inference; `simplify`
(`core/simplify.hpp`) performs cost-guided algebraic, trigonometric,
hyperbolic, and logarithmic simplification (respecting symbol assumptions); `solveSymbolic` and
`solveSystem2` (`core/symsolve.hpp`) solve parametric polynomial/radical
and single-occurrence transcendental equations and 2-variable polynomial
systems via Sylvester resultants; `taylor`, `laurent`, `limit`, `limitOneSided`, and `limitAtInfinity`
(`core/series.hpp`) compute truncated power/Laurent series and finite,
one-sided, and infinite (`inf` / `-inf`) symbolic limits.

**Polynomials** (`poly/`): `UPoly` — Q[x] with exact division,
squarefree decomposition; Sturm machinery (`isolateRealRoots`,
`refineRoot`); `solveRealRoots` — exact real roots (rationals as
values, irrationals as isolating brackets); `factorOverQ` — full
Zassenhaus factorization.

**Integration** (`integrate/`): `integrate(Ctx&, f, var, budget)` —
the unified proof-carrying integrator cascade combining the Rubi
discrimination-tree fast path with `integrateRational` (Hermite
reduction, Rothstein–Trager residues, quadratic and cubic
Rioboo-phase-A real atan/log forms, RootOf atoms where unavoidable,
and Liouvillian storeys for R(e^x), R(log x)/x, R(sin,cos) via
t=tan(x/2) and R(x^(p/q))) plus linearity over constant factors and
mixed sums; every answer passes a Tier-1 symbolic certificate AND a
Tier-2a certified interval audit of the form (a wrong form is
structurally impossible — it becomes an honest `Unevaluated`).
`definiteIntegrate(Ctx&, f, var, a, b, budget)` evaluates proper and
improper definite integrals via Newton–Leibniz and endpoint limits
with interior-pole detection and real $\log|u|$ branch realization.
`factorExpr` gives the factored form.

**Rubi fast path** (`rubi/`): `rubiApply(tables, Ctx&, f, var, budget)` —
the compiled discrimination-tree matcher over the Rubi R1–R5 slice
(60 `.m` files across `1.1` binomials, `1.2` trinomials, `2` exponentials,
`3` logarithms, `4` trigonometry, `5` inverse trig, `6` hyperbolics, and
`7` inverse hyperbolics; 2058 rules, 10301 trie nodes) with recursive
`Int`/`Subst`/`ExpandIntegrand` cascades and mirrors of Rubi's 9.1 utility
identities; every replacement passes the symbolic certificate.
`tools/rubi_parse.py` + `tools/rubi_codegen.py` regenerate the committed
tables from `third_party/rubi-snapshot/`.

**Symbolic Linear Algebra** (`linalg/`): `SymMatrix` over `Expr`,
rational expression normalizer `simplifyRationalExpr`, multivariable
calculus (`jacobian`, `gradient`, `hessian`), division-free
Faddeev–LeVerrier characteristic polynomial, determinant, adjugate,
and inverse (`charpoly`, `det`, `adjugate`, `inv`), exact linear
system solver (`linsolve`), RREF kernel basis (`nullspace`), symbolic
eigenvalues and eigenvectors (`eigenvalues`, `eigenvectors`), and
certified matrix exponential (`matrixExp`).

**Ordinary Differential Equations** (`ode/`): `dsolve1`, `dsolve1IVP`,
`dsolve2Linear`, `dsolve2LinearIVP`, `dsolveSystem1Linear`, and
`dsolveSystem1LinearIVP` (`ode/dsolve.hpp`) solve 1st-order quadrature,
linear, separable, and Bernoulli ODEs, 2nd-order constant-coefficient
linear ODEs (overdamped, critically damped, and underdamped oscillatory
regimes with resonant forcing and initial value problems), and $n \times n$
first-order constant-coefficient linear ODE systems $\mathbf{y}' = A\mathbf{y} + \mathbf{f}(x)$
(distinct real, repeated/defective Jordan blocks, and complex-conjugate
eigenvalues $\alpha \pm i\omega$, plus Cauchy IVPs), certifying every
solution by substitution into the ODE.

**Integral Transforms** (`transform/`): `laplace` and `ilaplace`
(`transform/laplace.hpp`) compute forward and inverse unilateral
Laplace transforms with frequency-shift, frequency-differentiation,
trig/hyperbolic product reduction, partial-fraction inversion over
$\mathbb{Q}[s]$ (including repeated complex-conjugate quadratic poles
and parametric forms), and mandatory round-trip certification
$\mathcal{L}\{\mathcal{L}^{-1}\{F\}\}(s) = F(s)$.

**Cancellation** (`core/budget.hpp`): `Budget` token tracking step and
arena-byte limits (`StepExhausted` / `ArenaExhausted`) across
factorization, rational/Liouvillian integration, Rubi, series, and
linear algebra.

## Vendoring into Numkit

```
python tools/vendor_sync.py --dest <numkit-tree>/third_party/numkit-cas
```

Copies the explicit whitelist (public headers + library sources,
nothing else) and writes a self-contained `CMakeLists.txt`; the
destination builds `numkit::cas` via a plain `add_subdirectory`.
`--dry-run` lists the copies. Integration contract (C++17, zero
dependencies, MSVC-portable, single-threaded, WASM-safe) is binding;
`notes/integration-model.md` has the design rationale.
