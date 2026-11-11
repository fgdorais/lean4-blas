/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS

/-!
# Benchmarks

Times the routines of `BLAS`, and compares each with a reference written with core's `FloatArray`
where there is one. The ratios are more meaningful than the times, since both sides run on the same
machine at the same moment.

Usage: `lake exe bench [--tsv] [size] [rounds]`. Each benchmark runs `rounds` times and reports
the fastest run. `--tsv` prints `name<TAB>milliseconds` lines, which
`scripts/bench_compare.py` uses to compare two builds.
-/

open ScalarArray

namespace BLASBench

/--
Runs `f` and returns its result. It is not inlined, so `f` runs exactly when this action does,
between the clock readings around it.
-/
@[noinline] def run (f : Nat → Float) (n : Nat) : IO Float := pure (f n)

/-- The fastest of `rounds` runs of `f n`, in milliseconds. -/
def time (rounds n : Nat) (f : Nat → Float) : IO Float := do
  let mut best := (0 : UInt64) - 1
  let mut sink : Float := 0
  for _ in [0:rounds] do
    let t₀ ← IO.monoNanosNow
    sink := sink + (← run f n)
    let t₁ ← IO.monoNanosNow
    best := min best (t₁ - t₀).toUInt64
  -- Keeps the results live.
  if sink == 0.125 then IO.eprintln ""
  return best.toFloat / 1e6

/-- One line of the results. -/
structure Row where
  /-- The benchmark's name. -/
  name : String
  /-- The time for `BLAS`, in milliseconds. -/
  time : Float
  /-- The time for the reference, in milliseconds, if there is one. -/
  ref : Option Float

/-- A vector of `n` elements computed from their indices. -/
def vec (n : Nat) : Float64Array := .ofFn (n := n) fun i => (i.val % 7).toFloat - 3

/-- The number of times each update runs per round: the first copies the shared input. -/
def reps : Nat := 10

/-- `α * x + y` on core's `FloatArray`, as a loop over `USize` indices with checked reads. -/
partial def refAxpy (α : Float) (x y : FloatArray) : FloatArray :=
  loop y 0
where
  /-- The loop from index `i`. -/
  loop (y : FloatArray) (i : USize) : FloatArray :=
    if h : i.toNat < y.size then
      if hx : i.toNat < x.size then loop (y.uset i (α * x.uget i hx + y.uget i h) h) (i + 1)
      else y
    else y

/-- `α * x` on core's `FloatArray`, as a loop over `USize` indices. -/
partial def refScal (α : Float) (x : FloatArray) : FloatArray :=
  loop x 0
where
  /-- The loop from index `i`. -/
  loop (x : FloatArray) (i : USize) : FloatArray :=
    if h : i.toNat < x.size then loop (x.uset i (α * x.uget i h) h) (i + 1) else x

/-- The dot product on core's `FloatArray`, as a loop over `USize` indices with checked reads. -/
partial def refDot (x y : FloatArray) : Float :=
  loop 0 0
where
  /-- The loop from index `i`. -/
  loop (i : USize) (s : Float) : Float :=
    if h : i.toNat < x.size then
      if hy : i.toNat < y.size then loop (i + 1) (s + x.uget i h * y.uget i hy) else s
    else s

/-- `iamax` on core's `FloatArray`, as a loop over `USize` indices. -/
partial def refIamax (x : FloatArray) : Nat :=
  loop 0 0 0
where
  /-- The loop from index `i`. -/
  loop (i : USize) (k : USize) (m : Float) : Nat :=
    if h : i.toNat < x.size then
      let a := (x.uget i h).abs
      if i == 0 || a > m then loop (i + 1) i a else loop (i + 1) k m
    else k.toNat

/-- The benchmarks. -/
def rows (rounds n : Nat) : IO (List Row) := do
  let x := vec n
  let x' := x.toFloatArray
  -- A baseline for the harness: a plain read-only loop over each array.
  let sum ← time rounds n fun _ => x.foldl (· + ·) 0
  let sum' ← time rounds n fun _ => x'.foldl (· + ·) 0
  let v : BLAS.Float64.Vec n := ⟨x, by simp [x, vec]⟩
  let axpy ← time rounds n fun _ => Id.run do
    let mut z := v
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.axpy 0.5 v z
    return z.data[0]!
  let axpy' ← time rounds n fun _ => Id.run do
    let mut z := x'
    for _ in [0:reps] do
      z := refAxpy 0.5 x' z
    return z[0]!
  let scal ← time rounds n fun _ => Id.run do
    let mut z := v
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.scal 0.5 z
    return z.data[0]!
  let scal' ← time rounds n fun _ => Id.run do
    let mut z := x'
    for _ in [0:reps] do
      z := refScal 0.5 z
    return z[0]!
  let w : BLAS.Float64.Vec n := .ofFn fun i => i.val.toFloat
  let copy ← time rounds n fun _ => Id.run do
    let mut z := w
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.copy v z
    return z.data[0]!
  let dot ← time rounds n fun _ => BLAS.Float64.Vec.dot v v
  let dot' ← time rounds n fun _ => refDot x' x'
  let asum ← time rounds n fun _ => BLAS.Float64.Vec.asum v
  let asum' ← time rounds n fun _ => x'.foldl (fun s a => s + a.abs) 0
  let nrm2 ← time rounds n fun _ => BLAS.Float64.Vec.nrm2 v
  let nrm2' ← time rounds n fun _ => (x'.foldl (fun s a => s + a * a) 0).sqrt
  let iamax ← time rounds n fun _ => (BLAS.Float64.Vec.iamax v).toFloat
  let iamax' ← time rounds n fun _ => (refIamax x').toFloat
  return [⟨"sum (baseline)", sum, some sum'⟩, ⟨s!"axpy ×{reps}", axpy, some axpy'⟩,
    ⟨s!"scal ×{reps}", scal, some scal'⟩, ⟨s!"copy ×{reps}", copy, none⟩,
    ⟨"dot", dot, some dot'⟩, ⟨"asum", asum, some asum'⟩, ⟨"nrm2", nrm2, some nrm2'⟩,
    ⟨"iamax", iamax, some iamax'⟩]

/-- A time in milliseconds with three decimals. -/
def fmt (t : Float) : String :=
  let s := toString ((t * 1000).round / 1000)
  match s.splitOn "." with
  | [i, f] => i ++ "." ++ (f ++ "000").take 3
  | _ => s

end BLASBench

open BLASBench in
/-- Runs the benchmarks and prints a Markdown table, or TSV with `--tsv`. -/
public def main (args : List String) : IO Unit := do
  let tsv := args.contains "--tsv"
  let nums := (args.filter (· != "--tsv")).filterMap String.toNat?
  let n := nums[0]?.getD 1_000_000
  let rounds := nums[1]?.getD 10
  let rows ← rows rounds n
  if tsv then
    for r in rows do
      IO.println s!"{r.name}\t{fmt r.time}"
  else
    IO.println s!"{n} elements, fastest of {rounds} runs, in milliseconds.\n"
    IO.println "| Benchmark | BLAS | Reference | Ratio |"
    IO.println "|---|--:|--:|--:|"
    for r in rows do
      let (c, ratio) := match r.ref with
        | some c => (fmt c, fmt (r.time / c))
        | none => ("—", "—")
      IO.println s!"| {r.name} | {fmt r.time} | {c} | {ratio} |"
