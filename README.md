# Lean 4 / BLAS

[![CI](https://github.com/fgdorais/lean4-blas/actions/workflows/cd-pipeline.yml/badge.svg)](https://github.com/fgdorais/lean4-blas/actions/workflows/cd-pipeline.yml)

Basic Linear Algebra Subprograms written entirely in Lean 4, on the unboxed arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays), with no C code of its own.
The routines come with proved specifications; their speed is measured, not promised.

The library is at an early stage: this is its scaffolding, and the Level 1 routines come next.

## Installation

The library depends only on lean4-scalar-arrays, pinned to an exact version, since the kernels use
its experimental `inplace` notation. The `main` branch follows the newest Lean release, including
release candidates, and the `nightly-testing` branch follows the newest Lean nightly.

## Development

```bash
lake build
```

```bash
lake test
```

The tests in `BLASTest` are `#guard` checks that run when the test library is built, so
`lake build` runs them as well, and CI builds with `--wfail`. Both libraries use
`precompileModules`, so the checks call the compiled code of scalar-arrays rather than evaluating
its Lean model.

`lake exe bench [--tsv] [size] [rounds]` times the routines and compares each with a reference on
core's `FloatArray` where there is one. `lake build` compiles it so that it keeps up with the API,
but CI doesn't run it. To run it on GitHub, add the `benchmark` label to a pull request, which
compares the pull request with its base, or start the Benchmarks workflow from the Actions tab.

You can generate the documentation locally with `lake build BLAS:docs` in the `docs` directory.

-----

* The `Lean 4 / BLAS` library is copyright © 2026 François G. Dorais. The library is released
  under the [Apache 2.0 license](https://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE
  for additional details.
