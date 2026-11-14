# Lean 4 / BLAS

[![CI](https://github.com/fgdorais/lean4-blas/actions/workflows/cd-pipeline.yml/badge.svg)](https://github.com/fgdorais/lean4-blas/actions/workflows/cd-pipeline.yml)

Basic Linear Algebra Subprograms written entirely in Lean 4, on the unboxed arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays), with no C code of its own.
The routines come with proved specifications; their speed is measured, not promised.

The library is at an early stage. It has, on `Float64` and `Float32`, the BLAS Level 1 routines on
strided vectors, and `gemv`, `ger`, `trsv` and `gemm` on matrices with an offset and a leading
dimension. The `Float32` routines are in `BLAS.Float32`, with the same names and specifications as
those of `BLAS.Float64`, on `Float32Array`.

## Usage

```lean
import BLAS

open BLAS.Float64

def x : Vec 3 := .ofList [1, 2, 3]
def y : Vec 3 := .ofList [4, 5, 6]

#eval (Vec.axpy 2 x y).toList  -- [6, 9, 12]
#eval Vec.dot x y              -- 32

example (α : Float) (hα : (α == 0) = false) (x y : Vec n) (i : Nat) (h : i < n) :
    (Vec.axpy α x y)[i] = α * x[i] + y[i] := by simp [hα]
```

`Vec n` is a vector of `n` floats, stored in a `Float64Array` with an offset `off` and a stride
`inc`, as in the reference BLAS: `x[i]` is at the index `off + inc * i`. The stride is positive,
unless `n ≤ 1`. `Vec.ofFn`, `Vec.ofList` and `Vec.ofArray` make contiguous vectors, and
`Vec.ofStride? a off inc` makes a strided view of the array `a`. Every routine has a specification
as an exact `Float` equality, in the order the routine evaluates. The routines follow the
semantics of the reference BLAS (Reference-LAPACK `master`), including its special cases, such as
`α = 0` in `axpy`, which returns `y` without reading `x`:

| Routine | Result | Specification |
|---|---|---|
| `axpy α x y` | `α * x + y`, over `y` | `if α == 0 then y[i] else α * x[i] + y[i]` |
| `scal α x` | `α * x`, over `x` | `(scal α x)[i] = α * x[i]` |
| `copy x y` | `x`, over `y` | `(copy x y)[i] = x[i]` |
| `swap x y` | `(y, x)` | `swap_fst`, `swap_snd` |
| `rot c s x y` | `(c * x + s * y, c * y - s * x)`, over `x` and `y` | `getElem_rot_fst`, `getElem_rot_snd` |
| `rotm p x y` | `H * (x, y)` for the modified rotation `p`, over `x` and `y` | `getElem_rotm_fst`, `getElem_rotm_snd` |
| `dot x y` | `Σ x[i] * y[i]` | `Nat.fold n (fun i h s => s + x[i] * y[i]) 0` |
| `asum x` | `Σ \|x[i]\|` | `Nat.fold n (fun i h s => s + x[i].abs) 0` |
| `nrm2 x` | `√(Σ x[i] * x[i])`, scaled | `nrm2Finish (Nat.fold n (nrm2Step x) (0, 0, 0))` |
| `iamax x` | index of the first largest `\|x[i]\|`, or first `NaN` | `(Nat.fold n (iamaxStep x) (0, 0)).1` |

The updates work in place when their output vector's array is not shared, and copy it once
otherwise. They leave the elements of the array outside the vector unchanged: `data_axpy` and the
other `data_` lemmas give the whole array as a scalar-arrays `modifyAt` of the old one, at the
indices `x.stride.idx i` of the vector. The loops are the same
for every stride, and run as fast at stride `1` as loops over contiguous indices.
`nrm2` is Blue's algorithm, as in the reference `dnrm2`: it sums the squares of the small, the
mid-range and the big elements in three accumulators, scaled by powers of `2`, so it overflows or
underflows only when the norm does. `iamax` counts from `0`, unlike the reference BLAS, and is `0`
for the empty vector.

`rotg a b` and `rotmg d1 d2 x1 y1` construct a rotation and a modified rotation, step for step as
the reference `drotg` and `drotmg`, and return their results in the structures `Rotg` and `Rotmg`
rather than in their arguments. A `RotmParam` is the reference `DPARAM`: its flag says which
entries of `H` `rotm` reads, and `rotmg` fills the others with the values the flag implies. Where
the reference `drotmg` loops forever, when `d1` or `d2` is or becomes infinite, `rotmg` stops after
`Rotmg.fuel` rescaling steps.

`Mat m n` is an `m × n` matrix, stored in column-major order with an offset `off` and a leading
dimension `ld ≥ m`, as in the reference BLAS: `A[(i, j)]` is at the index `off + ld * j + i`.
`Mat.ofFn` makes a packed matrix (`off = 0`, `ld = m`), and `Mat.ofLd? a off ld` makes a view of
the array `a`, such as a block of a larger matrix. `A.col j` and `A.row i` are vectors over the
same array, with no copy. `Mat.gemm α A B β C`, for `A : Mat m k`, `B : Mat k n` and
`C : Mat m n`, is `α * A * B + β * C`, over `C`, in the order of the reference BLAS:

```lean
(gemm α A B β C)[(i, j)] =
  if α == 0 then betaMul β C[(i, j)]
  else Nat.fold k (fun l _ s => s + α * B[(l, j)] * A[(i, l)]) (betaMul β C[(i, j)])
```

where `betaMul β v` is `β * v`, or `0` when `β = 0`: as in the reference BLAS, `β = 0` sets `C` to
`0` without reading it, so a `NaN` in `C` doesn't survive, and `α = 0` only scales `C`, without
reading `A` or `B`. `data_gemm` gives the whole array of the result, so the elements outside `C`
are unchanged.

`gemm` works on blocks of 256 rows and 128 terms, and sweeps the rows of a block for two columns
of `C` and four terms at a time, which the C compiler vectorizes. Each element still gets its terms
in the order of the specification. `Mat.gemmNaive` runs the naive loops of the reference BLAS, about
half as fast, and `gemm_eq_gemmNaive` proves that the results are the same to the bit.

Both run their kernels on packed matrices, `PMat m n`. A packed `Mat` goes to the kernel as it is,
and a packed `C` is updated in place. Any other matrix is packed into a copy first, one `memmove`
per column, and the columns of the result are copied back into `C`'s array.

The Level 2 routines run directly on any `Mat` and `Vec`, with no packing. Each element gets the
operations of the reference BLAS in its order, although `gemv` and `gemvT` handle four columns of
`A` per loop, and their specifications are exact in the same way:

| Routine | Result | Specification |
|---|---|---|
| `gemv α A x β y` | `α * A * x + β * y`, over `y` | `Nat.fold n (fun j _ s => s + α * x[j] * A[(i, j)]) (betaMul β y[i])` |
| `gemvT α A x β y` | `α * Aᵀ * x + β * y`, over `y` | `betaMul β y[j] + α * Nat.fold m (fun i _ s => s + A[(i, j)] * x[i]) 0` |
| `ger α x y A` | `α * x * yᵀ + A`, over `A` | `A[(i, j)] + x[i] * (α * y[j])`, or `A[(i, j)]` if `α = 0` or `y[j] = 0` |
| `trsv uplo diag A x` | `A⁻¹ * x` for a triangular `A`, over `x` | `getElem_trsv_lower`, `getElem_trsv_upper` |

These are the general cases. As in the reference BLAS, `gemv` and `gemvT` return `y` when the sum
is empty (`n = 0`, resp. `m = 0`), only scale `y` when `α = 0`, and set it to `0` without reading
it when `β = 0`; `ger` skips the columns with `y[j] = 0`. The `getElem_` lemmas state every case.

`trsv` takes the triangle as a `Uplo` (`.upper` or `.lower`) and the diagonal as a `Diag` (`.unit`
or `.nonUnit`), and reads nothing else of `A`. Its specification is back substitution, in the order of
the column-oriented loops: for the lower triangle, `y = trsv .lower d A x` satisfies

```lean
y[i] = d.apply (Nat.fold i (fun l _ s => s - y[l] * A[(i, l)]) x[i]) A[(i, i)]
```

where `d.apply v a` is `v / a`, or `v` for a unit diagonal. For the upper triangle, the terms run
from `l = n - 1` down to `i + 1`.

## Conformance

The target is the behavior of the reference BLAS, as in the current `master` branch of
[Reference-LAPACK](https://github.com/Reference-LAPACK/lapack), rather than its last release. Each
routine computes every element with the operations of the reference implementation, in the same
order, so that the result is exact to the bit, and its specification says so. Where a routine still
differs from the reference BLAS, such as `iamax` counting from `0`, its documentation says how.

## Performance

Speed comes second to proofs, and it is measured rather than promised. On the machines measured
so far, the routines match the reference BLAS on Level 1 and surpass it on Level 2, and `gemm` is
about 4 times faster than its `dgemm`.

Against OpenBLAS on one thread, we don't expect any routine to be more than about 5 times slower.
The Level 1 updates and the Level 2 routines run at about its speed, the reductions such as `dot`
and `iamax` at about half its speed, since their specifications fix the order of their operations,
and `gemm` is the furthest behind. OpenBLAS runs on several threads by default, and this
library runs on one, so on a multi-core machine the gap is larger. These figures are for `Float64`.
On `Float32`, whose vectors hold twice as many elements, the reductions and `gemm` fall further
behind OpenBLAS, to about 4 to 5 times slower. `scripts/blas_compare.py`, below, measures both
comparisons. [TODO.md](TODO.md) lists possible improvements.

### Compiler options

The library is compiled with Lean's default C compiler options, which target the baseline
instruction set of the platform, so that its binaries run on any machine of that architecture.
They include `-ffp-contract=off`, which keeps the C compiler from fusing a multiplication and an
addition into one rounding: the specifications depend on it. Never compile the library with
`-ffast-math`, `-ffp-contract=fast` or similar options, which change the results.

The lakefile adds `-falign-loops=64`, so that a loop's speed doesn't depend on where unrelated code
moves it. Adding `-march=native` to `moreLeancArgs` in `lakefile.toml` gives a modest speedup on
Level 2 and `gemm`, but the binaries then only run on CPUs like the one that built them.

## Installation

The library depends only on lean4-scalar-arrays, pinned to an exact version. The `main` branch
follows the newest Lean release, including release candidates, and the `nightly-testing` branch
follows the newest Lean nightly.

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

`lake exe bench [--tsv] [--float32] [size] [rounds]` times the `Float64` routines, or the
`Float32` ones with `--float32`, and compares each with a hand-written `USize` loop where there is
one. `lake build` compiles it so that it keeps up with the API,
but CI doesn't run it. To run it on GitHub, add the `benchmark` label to a pull request, which
compares the pull request with its base, or start the Benchmarks workflow from the Actions tab.

The `Float32` sources, tests and benchmarks, in `BLAS/Float32/`, `BLASTest/Float32/` and
`BLASBench/Float32.lean`, are generated from the `Float64` versions. Make changes in
`BLAS/Float64/`, `BLASTest/Float64/` and `BLASBench/Float64.lean`, then regenerate the `Float32`
files:

```bash
python3 scripts/generate.py
```

Text that depends on the precision, such as the constants of `nrm2` and test tolerances, is
translated by a table in the script, which fails if such text is left over.
`python3 scripts/generate.py --check` changes nothing and fails if a generated file is out of date;
CI runs it. The generated files are marked `linguist-generated` in `.gitattributes`, so GitHub
collapses them in diffs.

To compare with a C BLAS, such as OpenBLAS or Netlib's reference BLAS, build
`scripts/cblas_bench.c`, which runs the same benchmarks through the CBLAS interface of a shared
library that it loads at run time, and pass both outputs to `scripts/blas_compare.py`:

```
cc -O2 -o cblas_bench scripts/cblas_bench.c -ldl
lake exe bench --tsv > lean.tsv
OPENBLAS_NUM_THREADS=1 ./cblas_bench /usr/lib/x86_64-linux-gnu/libopenblas.so.0 > openblas.tsv
python3 scripts/blas_compare.py lean.tsv OpenBLAS=openblas.tsv
```

For `Float32`, compile `scripts/cblas_bench.c` with `-DSINGLE`, which times `sdot`, `sgemm` and
the other single-precision routines, and run `lake exe bench --tsv --float32`.

This is only a script: the library itself has no C dependency.

You can generate the documentation locally with `lake build BLAS:docs` in the `docs` directory.

-----

* The `Lean 4 / BLAS` library is copyright © 2026 François G. Dorais. The library is released
  under the [Apache 2.0 license](https://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE
  for additional details.
