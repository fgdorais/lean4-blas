# TODO: performance

Possible performance improvements, found by comparing with OpenBLAS 0.3.26 and the Netlib reference
BLAS through `scripts/blas_compare.py` (see the README). The ratios are OpenBLAS's speed on one
thread over ours, measured on a 4-core Xeon with AVX-512. The estimates come from C prototypes
compiled like our kernels (`-O3 -ffp-contract=off`, baseline x86-64), and are not promises.

Every item keeps the specifications exact, in the order of operations of the reference BLAS.
Changes that would reorder them, such as partial sums in `dot`, `asum` and `nrm2`, are left out.

## `gemm` (3.4–4.4× behind, 4.4–6× in `Float32`)

- Measured, not worth it: wider kernels. In C prototypes in the exact order, a sweep of four
  columns and four terms runs at the speed of the current two columns and four terms (about 20
  GFLOP/s), and register tiles that carry 16 or 32 accumulators across the terms, which would need
  `inplace` loops with more than four variables, run at 5–9 GFLOP/s, slower than the current
  kernel: each accumulator is one chain of dependent additions.
- [ ] Revisit packing `A` and `B` with a wider kernel. Packing the 256 × 128 block of `A` measured
  within noise with the current kernel.
- [ ] Parallel `gemm` over blocks of columns of `C`, with `Task`. Each column is independent, so
  the result stays the same to the bit. OpenBLAS on 4 threads is 10–18× ahead.

## Transposed `gemm`

- [ ] `gemmTN`, `gemmTT`: compute two columns of `C` per pass over four columns of `A`, so that
  each pass reads `A` once for two columns of `B`. They run at about 7.5 GFLOP/s at 256–1024, half
  of `gemm`, since each column of `C` reads all of `A`. Each sum keeps its order. Not measured yet.

## `gemmtr`

- [ ] `gemmtr`, `gemmtrNT`: run the kernel of `gemm`, two columns and four terms at a time, on the
  rows of each column in the triangle. They run at 5.3–7.7 GFLOP/s at 64–1024, at the speed of
  `gemmNaive`, one column and one term at a time, against 16–20 for `gemm`. Each element keeps its
  order of terms. Not measured yet.

## `syrk`, `syrkT`, `trsm` and `trsmRight` (6.6–9.3×, 8–11×, 2.2–4.5× and 3–8× behind at 256–1024)

- [x] `syrkT`: compute four elements of a column at a time, with the sums of `gemvT`. About 2×.
- [ ] `syrk`: sweep the rows of a block for several terms at a time, as `gemm` does. Each element
  keeps its order of terms, including the skipped ones.
- [x] `syrk`: two columns at a time, which share the reads of each column of `A`, with each column's
  skipped terms kept. About 1.5×.
- [x] `trsm`: solve four columns of `B` at a time, which share the reads of `A`. The columns are
  independent, so each keeps its order of operations. About 2× at 1024, where a column at a time
  read all of `A` from memory for each column, and 1–1.2× at 256.
- [ ] `trsmRight`: subtract four solved columns per pass over the rows of column `j`, as `gemv` adds
  four columns, so that each element keeps its order of operations. It is 3× behind at 256 and 8×
  at 1024, where `trsm` is 2.2× and 4.5×. Not measured yet.
- [ ] `trsmT`: solve four columns of `B` at a time, as `trsm` does. It is about 3× slower than
  `trsm` at 256–1024 (3.1 GFLOP/s), solving one column at a time by dot products.
- [ ] `trsmRightT`: fuse the solve of a column with the subtractions from the columns still to
  solve, as `trsmRight` does. It is 6× slower than `trsmRight` at 256, 4.2× at 512 and 2× at 1024
  (1.6–3.4 GFLOP/s), since each element reads a row of `A` with a stride.
- [ ] `trmm`, `trmmRight`, `trmmRightT`: four columns of `B` at a time, as `trsm` does, or four
  added columns per pass over the rows, as `gemv` adds four columns. Each element keeps its order
  of operations. They run at 1–1.9× the time of `trsm` and `trsmRight` (4.5–8.2 GFLOP/s at
  256–1024), one column at a time.
- [ ] `trmmT`: four columns at a time, which share the reads of `A`, each with its dot products in
  their order. It runs at 2.2–3.3× the time of `trsm` (2.8–4.2 GFLOP/s), like `trsmT`.
- [ ] `symm`, `symmRight`: as `trmm` and `trmmRight`, four columns of `C` at a time, or four added
  columns of `B` per pass over the rows of a column of `C`. Each element keeps its order of
  operations. They run at 5.4–7.8 GFLOP/s at 256–1024, one column at a time. Not measured yet.
- [ ] `syr2k`: two columns at a time, as `syrk` does, with each column's skipped terms kept. It runs
  at 5.2–7.3 GFLOP/s at 256–1024, one column at a time.
- [ ] `trsm`, `trsmRight`: update the rest of `B` by the `gemm` kernel after each block of solved
  rows or columns. This changes the order of the updates of an element only if the blocks reorder
  its terms, so it needs care to stay exact.

## `iamax` (1.6–1.9× behind, 2.4× in `Float32`)

- [ ] Find the largest `|x[i]|` with several independent running maxima, then the first index that
  holds it: 4× faster on typical data, 1.6× in the worst case, with the same result. Proving it
  needs order lemmas on `Float` that core doesn't have yet: `<` is a strict total order on
  non-`NaN` floats, no comparison with `NaN` is true, and `|x|` is `NaN` only when `x` is. Propose
  them to core, for `Float` and `Float32`.

## Level 2 (0.9–1.3× at 1024 and 2048, 1.2–1.8× at 256)

- [ ] `trmvT`, like `trsvT` below: it runs at about 1.5–2× the time of `trmv`, which runs at the
  speed of `trsv`. Each element is a dot product of a column with `x`, so four columns at a time
  share the reads of `x`, each with its terms in their order. Not measured yet.
- [ ] `trsvT`: compute four elements at a time, as `gemvT` computes four dot products, with each
  element's terms in their order: the next three elements depend only on the terms solved so far,
  except for a 4 × 4 triangle at the end. It runs at 3.2–4.5 GFLOP/s at 256–2048, about half of
  `trsv`. Not measured yet.

- [ ] `trsv`: update the rest of `x` four columns at a time after each block of four solved
  elements, as `gemv` does. Each element keeps its order of operations. Not measured yet.
- [ ] `gemv` with strided `x` and `y` is 1.05–3× behind, and 2.4–7.4× behind in `Float32`, where
  Netlib is also up to 6% faster at 256 and 1024. Not investigated yet.
- [ ] The band routines `gbmv`, `gbmvT`, `sbmv`, `tbmv`, `tbmvT`, `tbsv` and `tbsvT` are not
  benchmarked yet, against `scripts/cblas_bench.c` or otherwise. They run the loops of the reference
  BLAS one column at a time; `gbmv` and `sbmv` could take two or four columns per pass, as `gemv`
  does, with each element's terms in their order.
- [ ] The packed routines `spmv`, `spr`, `spr2`, `tpmv`, `tpmvT`, `tpsv` and `tpsvT` are not
  benchmarked yet either. They run the loops of the reference BLAS one column at a time, with the
  packed index computed per element; `spmv` could take two columns per pass, as `symv` does.
- [ ] `gemvT` at 256 is 1.8× behind, and 4.5× in `Float32`, against 1.0–1.1× (1.6–1.7× in
  `Float32`) at 1024 and 2048. Not investigated yet.

## Build

- [ ] An opt-in Lake option for `-march=native`, which gives 10–30% on Level 2 and `gemm` and
  nothing on Level 1, but makes binaries that only run on CPUs like the one that built them. The
  tests pass with it, since `-ffp-contract=off` stays on.
