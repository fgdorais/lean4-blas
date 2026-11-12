# Lean 4 / BLAS

[![CI](https://github.com/fgdorais/lean4-blas/actions/workflows/cd-pipeline.yml/badge.svg)](https://github.com/fgdorais/lean4-blas/actions/workflows/cd-pipeline.yml)

Basic Linear Algebra Subprograms written entirely in Lean 4, on the unboxed arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays), with no C code of its own.
The routines come with proved specifications; their speed is measured, not promised.

The library is at an early stage. It has the BLAS Level 1 routines and `gemm` on `Float64`; strided
vectors and Level 2 come next.

## Usage

```lean
import BLAS

open BLAS.Float64

def x : Vec 3 := .ofList [1, 2, 3]
def y : Vec 3 := .ofList [4, 5, 6]

#eval (Vec.axpy 2 x y).toList  -- [6, 9, 12]
#eval Vec.dot x y              -- 32

example (α : Float) (x y : Vec n) (i : Nat) (h : i < n) :
    (Vec.axpy α x y)[i] = α * x[i] + y[i] := by simp
```

`Vec n` is a vector of `n` floats, stored contiguously in a `Float64Array`. Every routine has a
specification as an exact `Float` equality, in the order the routine evaluates:

| Routine | Result | Specification |
|---|---|---|
| `axpy α x y` | `α * x + y`, over `y` | `(axpy α x y)[i] = α * x[i] + y[i]` |
| `scal α x` | `α * x`, over `x` | `(scal α x)[i] = α * x[i]` |
| `copy x y` | `x`, over `y` | `(copy x y)[i] = x[i]` |
| `swap x y` | `(y, x)` | `swap_fst`, `swap_snd` |
| `dot x y` | `Σ x[i] * y[i]` | `Nat.fold n (fun i h s => s + x[i] * y[i]) 0` |
| `asum x` | `Σ \|x[i]\|` | `Nat.fold n (fun i h s => s + x[i].abs) 0` |
| `nrm2 x` | `√(Σ x[i] * x[i])` | `(Nat.fold n (fun i h s => s + x[i] * x[i]) 0).sqrt` |
| `iamax x` | index of the first largest `\|x[i]\|` | `(Nat.fold n (iamaxStep x) (0, 0)).1` |

The updates work in place when their output vector is not shared, and copy it once otherwise.
`nrm2` doesn't scale its elements, so unlike the reference BLAS it can overflow or underflow.

`Mat m n` is an `m × n` matrix, stored contiguously in column-major order: `A[(i, j)]` is at the
index `i + m * j`. `Mat.gemm α A B β C`, for `A : Mat m k`, `B : Mat k n` and `C : Mat m n`, is
`α * A * B + β * C`, over `C`, in the order of the reference BLAS:

```lean
(gemm α A B β C)[(i, j)] =
  Nat.fold k (fun l _ s => s + α * B[(l, j)] * A[(i, l)]) (β * C[(i, j)])
```

Unlike the reference BLAS, `β = 0` doesn't clear `C`, so a `NaN` in `C` stays a `NaN`.

`Mat.gemmBlocked` computes the same matrix about twice as fast. It works on blocks of 256 rows and
128 terms, and sweeps the rows of a block for two columns of `C` and four terms at a time, which
the C compiler vectorizes. Each element still gets its terms in the order of the specification, so
`gemmBlocked_eq` proves that the result is the same to the bit, with the same `getElem` lemma.

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

`lake exe bench [--tsv] [size] [rounds]` times the routines and compares each with a hand-written
`USize` loop where there is one. `lake build` compiles it so that it keeps up with the API,
but CI doesn't run it. To run it on GitHub, add the `benchmark` label to a pull request, which
compares the pull request with its base, or start the Benchmarks workflow from the Actions tab.

You can generate the documentation locally with `lake build BLAS:docs` in the `docs` directory.

-----

* The `Lean 4 / BLAS` library is copyright © 2026 François G. Dorais. The library is released
  under the [Apache 2.0 license](https://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE
  for additional details.
