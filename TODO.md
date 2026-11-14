# TODO: performance

Possible performance improvements, found by comparing with OpenBLAS 0.3.26 and the Netlib reference
BLAS through `scripts/blas_compare.py` (see the README). The ratios are OpenBLAS's speed on one
thread over ours, measured on a 4-core Xeon with AVX-512. The estimates come from C prototypes
compiled like our kernels (`-O3 -ffp-contract=off`, baseline x86-64), and are not promises.

Every item keeps the specifications exact, in the order of operations of the reference BLAS.
Changes that would reorder them, such as partial sums in `dot`, `asum` and `nrm2`, are left out.

## `gemm` (4–5× behind)

- [ ] A wider register kernel than two columns of `C` and four terms, such as four columns and four
  terms, so that each load of `A` feeds more products. Each element keeps its order of terms, so
  `gemm_eq_gemmNaive` still holds.
- [ ] Revisit packing `A` and `B` with a wider kernel. Packing the 256 × 128 block of `A` measured
  within noise with the current kernel.
- [ ] Parallel `gemm` over blocks of columns of `C`, with `Task`. Each column is independent, so
  the result stays the same to the bit. OpenBLAS on 4 threads is 10–18× ahead.

## `iamax` (about 2× behind)

- [ ] Find the largest `|x[i]|` with several independent running maxima, then the first index that
  holds it: 4× faster on typical data, 1.6× in the worst case, with the same result. Proving it
  needs order lemmas on `Float` that core doesn't have yet: `<` is a strict total order on
  non-`NaN` floats, no comparison with `NaN` is true, and `|x|` is `NaN` only when `x` is. Propose
  them to core, for `Float` and `Float32`.

## Level 2 (0.8–1.2× at 1024 and 2048)

- [ ] `trsv`: update the rest of `x` four columns at a time after each block of four solved
  elements, as `gemv` does. Each element keeps its order of operations. Not measured yet.
- [ ] `gemv` with strided `x` and `y` is 1.3–1.5× behind. Not investigated yet.

## Build

- [ ] An opt-in Lake option for `-march=native`, which gives 10–30% on Level 2 and `gemm` and
  nothing on Level 1, but makes binaries that only run on CPUs like the one that built them. The
  tests pass with it, since `-ffp-contract=off` stays on.
- [ ] Benchmark `Float32` and compare with `sgemm` and the other single-precision routines. The
  `bench` exe is `Float64` only.
