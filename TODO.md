# TODO: performance

Possible performance improvements, found by comparing with OpenBLAS 0.3.26 and the Netlib reference
BLAS through `scripts/blas_compare.py` (see the README). The ratios are OpenBLAS's speed on one
thread over ours, measured on a 4-core Xeon with AVX-512. The estimates come from C prototypes
compiled like our kernels (`-O3 -ffp-contract=off`, baseline x86-64), and are not promises.

Every item keeps the specifications exact, in the order of operations of the reference BLAS.
Changes that would reorder them, such as partial sums in `dot`, `asum` and `nrm2`, are left out.

## `gemm` (4–5× behind)

- Measured, not worth it: wider kernels. In C prototypes in the exact order, a sweep of four
  columns and four terms runs at the speed of the current two columns and four terms (about 20
  GFLOP/s), and register tiles that carry 16 or 32 accumulators across the terms, which would need
  `inplace` loops with more than four variables, run at 5–9 GFLOP/s, slower than the current
  kernel: each accumulator is one chain of dependent additions.
- [ ] Revisit packing `A` and `B` with a wider kernel. Packing the 256 × 128 block of `A` measured
  within noise with the current kernel.
- [ ] Parallel `gemm` over blocks of columns of `C`, with `Task`. Each column is independent, so
  the result stays the same to the bit. OpenBLAS on 4 threads is 10–18× ahead.

## `syrk` and `trsm` (8–19× and 2–7× behind at 256–1024)

- [ ] `syrkT`: compute four elements of a column at a time, which share the reads of column `j` of
  `A` and give four independent chains of additions, as `gemvT` does with four columns. A C
  prototype in the exact order runs 2× faster with four, and no faster with eight or sixteen.
- [ ] `syrk`: sweep the rows of a block for several terms at a time, as `gemm` does. Each element
  keeps its order of terms, including the skipped ones.
- [ ] `trsm`, `trsmRight`: update the rest of `B` by the `gemm` kernel after each block of solved
  rows or columns. This changes the order of the updates of an element only if the blocks reorder
  its terms, so it needs care to stay exact.

## `iamax` (about 2× behind)

- [ ] Find the largest `|x[i]|` with several independent running maxima, then the first index that
  holds it: 4× faster on typical data, 1.6× in the worst case, with the same result. Proving it
  needs order lemmas on `Float` that core doesn't have yet: `<` is a strict total order on
  non-`NaN` floats, no comparison with `NaN` is true, and `|x|` is `NaN` only when `x` is. Propose
  them to core, for `Float` and `Float32`.

## Level 2 (0.8–1.2× at 1024 and 2048)

- [ ] `trsv`: update the rest of `x` four columns at a time after each block of four solved
  elements, as `gemv` does. Each element keeps its order of operations. Not measured yet.
- [ ] `gemv` with strided `x` and `y` is 1.3–1.5× behind, and 3.4–6.6× behind in `Float32`, where
  Netlib is also 7–12% faster. Not investigated yet.

## Build

- [ ] An opt-in Lake option for `-march=native`, which gives 10–30% on Level 2 and `gemm` and
  nothing on Level 1, but makes binaries that only run on CPUs like the one that built them. The
  tests pass with it, since `-ffp-contract=off` stays on.
