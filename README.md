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
