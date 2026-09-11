# numkit-cas

Symbolic computation core for [Numkit](https://github.com/hotredman/numkit):
exact arithmetic, hash-consed expression DAG, symbolic integration with
proof-carrying verification.

Pure C++17, zero external dependencies (WASM-safe, PMR-compatible memory).
Designed to be vendored into the Numkit tree as the `symbolic` toolbox core;
integration constraints (C++17, no deps, single-threaded base, PMR) are
binding for all code in this repository.

Specification: `notes/cas-integrator-plan.md` (v0.4).

## Layout

```
include/numkit/cas/...   public headers
src/...                  implementation (one .cpp per header)
tests/...                gtest suite (nkcas_gtest)
```

## Build & test

```
cmake -S . -B build/msvc -G "Visual Studio 17 2022" -A x64
cmake --build build/msvc --config Release
ctest --test-dir build/msvc -C Release --output-on-failure
```

## API surface (by layer)

All types live in `numkit::cas`. One `Ctx` owns the interned
expression arena; `Expr` handles are meaningful only inside their
`Ctx`.

**Exact numbers** (`num/`): `BigInt` — arbitrary-precision integers
(Miller-Rabin `isPrime`, Pollard-Brent `factorize`); `Rational` —
canonical exact rationals, `fromDoubleBits(double)` converts any
finite IEEE double losslessly.

**Expressions** (`core/`): `Ctx::symbol/number/add/mul/pow/func/
neg/div/rootOf` build a canonical hash-consed DAG (structural
equality is pointer identity); `parseExpr(Ctx&, src)` parses
MATLAB-precedence text; `toString` prints round-trip-exact forms;
`diff` differentiates (exp, log, sin, cos, tan, atan); `subs`
substitutes subtrees; `expand` distributes to polynomial form;
`evalExact` evaluates exactly in Q with honest declines outside.

**Polynomials** (`poly/`): `UPoly` — Q[x] with exact division,
squarefree decomposition; Sturm machinery (`isolateRealRoots`,
`refineRoot`); `solveRealRoots` — exact real roots (rationals as
values, irrationals as isolating brackets); `factorOverQ` — full
Zassenhaus factorization.

**Integration** (`integrate/`): `integrateRational(Ctx&, f, var)` —
the proof-carrying integrator: any rational function (Trager
residues incl. RootOf atoms), plus the Liouvillian storeys for
rational functions of exp(x), log(x)/x and sin/cos(x); every answer
carries a Tier-1 certificate or is an honest `Unevaluated`.
`factorExpr` gives the factored form.

**Cancellation** (`core/budget.hpp`): `Budget` token, the day-one
plumbing for the future speculative cascade.

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
