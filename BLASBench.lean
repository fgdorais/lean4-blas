/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLASBench.Basic
import BLASBench.Float64
import BLASBench.Float32

/-!
# Benchmarks

Times the routines of `BLAS`, and compares each with a hand-written reference loop where there is
one. The ratios are more meaningful than the times, since both sides run on the same
machine at the same moment.

Usage: `lake exe bench [--tsv] [--float32] [size] [rounds]`. Each benchmark runs `rounds` times and
reports the fastest run. It times the `Float64` routines, or the `Float32` ones with `--float32`.
`--tsv` prints `name<TAB>milliseconds` lines, which `scripts/bench_compare.py` uses to compare two
builds, and `scripts/blas_compare.py` to compare with a C BLAS.
-/

open BLASBench in
/-- Runs the benchmarks and prints a Markdown table, or TSV with `--tsv`. -/
public def main (args : List String) : IO Unit := do
  let tsv := args.contains "--tsv"
  let single := args.contains "--float32"
  let nums := (args.filter fun a => a != "--tsv" && a != "--float32").filterMap String.toNat?
  let n := nums[0]?.getD 1_000_000
  let rounds := nums[1]?.getD 10
  let base ← baseline rounds n
  let (rows, level2, gemm, level3) ←
    if single then BLASBench.Float32.all rounds n else BLASBench.Float64.all rounds n
  let rows := base :: rows ++ (level2.map (·.1)).flatten ++ (gemm.map (·.1)).flatten ++
    (level3.map (·.1)).flatten
  if tsv then
    for r in rows do
      IO.println s!"{r.name}\t{fmt r.time}"
  else
    IO.println
      s!"{if single then "Float32" else "Float64"}, {n} elements, fastest of {rounds} runs, in milliseconds.\n"
    IO.println "| Benchmark | BLAS | Reference | Ratio |"
    IO.println "|---|--:|--:|--:|"
    for r in rows do
      let (c, ratio) := match r.ref with
        | some c => (fmt c, fmt (r.time / c))
        | none => ("—", "—")
      IO.println s!"| {r.name} | {fmt r.time} | {c} | {ratio} |"
    IO.println "\nLevel 2 on square matrices, in GFLOP/s.\n"
    IO.println "| Size | gemv | gemvT | ger | gemv, stride 2 | trsv, lower | trsv, upper |"
    IO.println "|--:|--:|--:|--:|--:|--:|--:|"
    for (rs, flops) in level2, m in level2Sizes do
      let g (t : Float) := fmt (flops.toFloat / (t * 1e6))
      match rs with
      | [v, t, r, v2, tl, tu] =>
        IO.println
          s!"| {m} | {g v.time} | {g t.time} | {g r.time} | {g v2.time} | {g (2 * tl.time)} | {g (2 * tu.time)} |"
      | _ => pure ()
    IO.println "\n`gemm` of square matrices, in GFLOP/s.\n"
    IO.println "| Size | gemmNaive | gemm | gemm, ld = m + 8 | Reference |"
    IO.println "|--:|--:|--:|--:|--:|"
    for (rs, flops) in gemm, m in gemmSizes do
      let g (t : Float) := fmt (flops.toFloat / (t * 1e6))
      match rs with
      | [r, rb, rl] =>
        IO.println s!"| {m} | {g r.time} | {g rb.time} | {g rl.time} | {(r.ref.map g).getD "—"} |"
      | _ => pure ()
    IO.println "\n`syrk` and `trsm` of square matrices, in GFLOP/s.\n"
    IO.println "| Size | syrk, lower | syrkT, lower | trsm, lower | trsmRight, upper |"
    IO.println "|--:|--:|--:|--:|--:|"
    for (rs, flops) in level3, m in level3Sizes do
      let g (t : Float) := fmt (flops.toFloat / (t * 1e6))
      match rs with
      | [s, t, l, r] =>
        IO.println s!"| {m} | {g s.time} | {g t.time} | {g l.time} | {g r.time} |"
      | _ => pure ()
