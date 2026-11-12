/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS

/-!
# Benchmarks

Times the routines of `BLAS`, and compares each with a hand-written reference loop where there is
one. The ratios are more meaningful than the times, since both sides run on the same
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

/-- An index below `a.usize` is a valid index of `a`. -/
theorem lt_size_of_lt_usize {a : Float64Array} {i : USize} (h : i < a.usize) : i.toNat < a.size :=
  Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp h) a.toNat_usize_le

/-
The references are hand-written loops over `USize` indices bounded by `usize`, with unchecked reads
and writes, so that a ratio below 1 isn't due to a slow reference. They use scalar-arrays'
`Float64Array`, whose `uget` and `uset` compile to the same code as core's `FloatArray` ones, since
core has no lemmas on `FloatArray.usize` and `FloatArray.uset` to prove the indices valid.
-/

/-- `α * x + y`. -/
partial def refAxpy (α : Float) (x y : Float64Array) : Float64Array :=
  if hs : x.size = y.size then loop hs y rfl 0 else y
where
  /-- The loop from index `i`, over `z` of the size of `y`. -/
  loop (hs : x.size = y.size) (z : Float64Array) (hz : z.size = y.size) (i : USize) :
      Float64Array :=
    if h : i < x.usize then
      have hx := lt_size_of_lt_usize h
      loop hs (z.uset i (α * x.uget i hx + z.uget i (by omega)) (by omega)) (by simp [hz]) (i + 1)
    else z

/-- `α * x`. -/
partial def refScal (α : Float) (x : Float64Array) : Float64Array :=
  loop x.usize x x.toNat_usize_le 0
where
  /-- The loop from index `i`, up to `m`, which is at most the size of `z`. -/
  loop (m : USize) (z : Float64Array) (hm : m.toNat ≤ z.size) (i : USize) : Float64Array :=
    if h : i < m then
      have hi : i.toNat < z.size := Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp h) hm
      loop m (z.uset i (α * z.uget i hi) hi) (by simpa using hm) (i + 1)
    else z

/-- The dot product. -/
partial def refDot (x y : Float64Array) : Float :=
  if hs : x.size = y.size then loop hs 0 0 else 0
where
  /-- The loop from index `i`. -/
  loop (hs : x.size = y.size) (i : USize) (s : Float) : Float :=
    if h : i < x.usize then
      have hx := lt_size_of_lt_usize h
      loop hs (i + 1) (s + x.uget i hx * y.uget i (by omega))
    else s

/-- A sum of `f x[i]`. -/
@[specialize] partial def refSum (f : Float → Float) (x : Float64Array) : Float :=
  loop 0 0
where
  /-- The loop from index `i`. -/
  @[specialize] loop (i : USize) (s : Float) : Float :=
    if h : i < x.usize then loop (i + 1) (s + f (x.uget i (lt_size_of_lt_usize h))) else s

/-- `iamax`. -/
partial def refIamax (x : Float64Array) : Nat :=
  loop 0 0 0
where
  /-- The loop from index `i`. -/
  loop (i : USize) (k : USize) (m : Float) : Nat :=
    if h : i < x.usize then
      let a := (x.uget i (lt_size_of_lt_usize h)).abs
      if i == 0 || a > m then loop (i + 1) i a else loop (i + 1) k m
    else k.toNat

/-- The size facts that the reference `gemm` loops need, for `m × m` matrices. -/
structure GemmSizes (m : USize) (a b c : Float64Array) : Prop where
  ha : a.size = m.toNat * m.toNat
  hb : b.size = a.size
  hc : c.size = a.size
  hs : a.size < USize.size

/-- Column `j < m` of an `m × m` matrix fits in an array of `m * m` elements. -/
theorem col_le {m j : USize} {a b c : Float64Array} (h : GemmSizes m a b c) (hj : j < m) :
    (m * j).toNat + m.toNat ≤ a.size :=
  BLAS.Float64.toNat_mul_add_le (n := m.toNat) (USize.lt_iff_toNat_lt.mp hj) (by rw [h.ha]; exact Nat.le_refl _) h.hs

/-- The element `off + i` of a column at `off`, for `i < m`. -/
theorem idx_lt {m off i : USize} {p : Nat} (hw : off.toNat + m.toNat ≤ p) (hi : i < m) :
    (off + i).toNat < p :=
  ScalarArray.InPlaceSyntax.toNat_add_lt_of_window hw (USize.lt_iff_toNat_lt.mp hi)

/--
`α * A * B + β * C` for `m × m` matrices, by the loops of the naive `gemm`: for each column `j` of
`C`, scale it by `β`, then add `α * B[l, j]` times column `l` of `A`.
-/
partial def refGemm (m : USize) (α : Float) (a b : Float64Array) (β : Float) (c : Float64Array) :
    Float64Array :=
  if h : a.size = m.toNat * m.toNat ∧ b.size = a.size ∧ c.size = a.size ∧ a.size < USize.size then
    (cols ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩ ⟨c, h.2.2.1⟩ 0).1
  else c
where
  /-- The columns from `j`. -/
  cols (h : GemmSizes m a b c) (z : {z : Float64Array // z.size = a.size}) (j : USize) :
      {z : Float64Array // z.size = a.size} :=
    if hj : j < m then
      have hw := col_le h hj
      let z := scale z (m * j) (by rw [z.2]; exact hw) 0
      cols h (terms h z j hj 0) (j + 1)
    else z
  /-- Scales `z[cj + i]`, for the indices from `i`. -/
  scale (z : {z : Float64Array // z.size = a.size}) (cj : USize)
      (hw : cj.toNat + m.toNat ≤ z.1.size) (i : USize) : {z : Float64Array // z.size = a.size} :=
    if hi : i < m then
      have hi := idx_lt hw hi
      scale ⟨z.1.uset (cj + i) (β * z.1.uget (cj + i) hi) hi, by simp [z.2]⟩ cj
        (by simpa using hw) (i + 1)
    else z
  /-- Adds the terms of column `j`, for the indices from `l`. -/
  terms (h : GemmSizes m a b c) (z : {z : Float64Array // z.size = a.size}) (j : USize)
      (hj : j < m) (l : USize) : {z : Float64Array // z.size = a.size} :=
    if hl : l < m then
      have hb := idx_lt (by rw [h.hb]; exact col_le h hj) hl
      let t := α * b.uget (m * j + l) hb
      terms h (axpyCol h z t (m * j) (by rw [z.2]; exact col_le h hj) (m * l) (col_le h hl) 0) j
        hj (l + 1)
    else z
  /-- `z[cj + i] += t * a[al + i]`, for the indices from `i`. -/
  axpyCol (h : GemmSizes m a b c) (z : {z : Float64Array // z.size = a.size}) (t : Float)
      (cj : USize) (hw : cj.toNat + m.toNat ≤ z.1.size) (al : USize)
      (ha : al.toNat + m.toNat ≤ a.size) (i : USize) : {z : Float64Array // z.size = a.size} :=
    if hi : i < m then
      have hz := idx_lt hw hi
      axpyCol h ⟨z.1.uset (cj + i) (z.1.uget (cj + i) hz + t * a.uget (al + i) (idx_lt ha hi)) hz,
        by simp [z.2]⟩ t cj (by simpa using hw) al ha (i + 1)
    else z

/-- The benchmarks. -/
def rows (rounds n : Nat) : IO (List Row) := do
  let x := vec n
  let x' := x.toFloatArray
  -- A baseline for the harness: a plain read-only loop over each array.
  let sum ← time rounds n fun _ => x.foldl (· + ·) 0
  let sum' ← time rounds n fun _ => x'.foldl (· + ·) 0
  let v : BLAS.Float64.Vec n := .ofArray x (by simp [x, vec])
  let axpy ← time rounds n fun _ => Id.run do
    let mut z := v
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.axpy 0.5 v z
    return z.data[0]!
  let axpy' ← time rounds n fun _ => Id.run do
    let mut z := x
    for _ in [0:reps] do
      z := refAxpy 0.5 x z
    return z[0]!
  let scal ← time rounds n fun _ => Id.run do
    let mut z := v
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.scal 0.5 z
    return z.data[0]!
  let scal' ← time rounds n fun _ => Id.run do
    let mut z := x
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
  let dot' ← time rounds n fun _ => refDot x x
  let asum ← time rounds n fun _ => BLAS.Float64.Vec.asum v
  let asum' ← time rounds n fun _ => refSum (·.abs) x
  let nrm2 ← time rounds n fun _ => BLAS.Float64.Vec.nrm2 v
  let nrm2' ← time rounds n fun _ => (refSum (fun a => a * a) x).sqrt
  let iamax ← time rounds n fun _ => (BLAS.Float64.Vec.iamax v).toFloat
  let iamax' ← time rounds n fun _ => (refIamax x).toFloat
  -- The worst case for `iamax`: every element is a new maximum.
  let up : BLAS.Float64.Vec n := .ofFn fun i => i.val.toFloat
  let iamaxUp ← time rounds n fun _ => (BLAS.Float64.Vec.iamax up).toFloat
  let iamaxUp' ← time rounds n fun _ => (refIamax up.data).toFloat
  -- Strided vectors: every other element of an array of `2 * n`, against the contiguous ones.
  let x2 := vec (2 * n)
  let v2 : BLAS.Float64.Vec n := (BLAS.Float64.Vec.ofStride? x2 0 2).getD v
  let axpy2 ← time rounds n fun _ => Id.run do
    let mut z := v2
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.axpy 0.5 v2 z
    return z.data[0]!
  let dot2 ← time rounds n fun _ => BLAS.Float64.Vec.dot v2 v2
  return [⟨"sum (baseline)", sum, some sum'⟩, ⟨s!"axpy ×{reps}", axpy, some axpy'⟩,
    ⟨s!"scal ×{reps}", scal, some scal'⟩, ⟨s!"copy ×{reps}", copy, none⟩,
    ⟨"dot", dot, some dot'⟩, ⟨"asum", asum, some asum'⟩, ⟨"nrm2", nrm2, some nrm2'⟩,
    ⟨"iamax", iamax, some iamax'⟩, ⟨"iamax (increasing)", iamaxUp, some iamaxUp'⟩,
    ⟨s!"axpy ×{reps}, stride 2 / stride 1", axpy2, some axpy⟩,
    ⟨"dot, stride 2 / stride 1", dot2, some dot⟩]

/-- An `m × m` matrix computed from its indices. -/
def mat (m s : Nat) : BLAS.Float64.Mat m m :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat - 5

/-- The sizes of the `gemm` benchmarks. -/
def gemmSizes : List Nat := [64, 256, 512, 1024]

/--
The `gemm` benchmarks for `m × m` matrices: the rows of `gemm` and `gemmBlocked`, and their
floating-point operations. Each timed call depends on its argument, which is `m`, so that the
compiler can't hoist it out of the timing loop.
-/
def gemmRows (rounds m : Nat) : IO (List Row × Nat) := do
  let A := mat m 1
  let B := mat m 2
  let C := mat m 3
  let α (q : Nat) := 1.5 + (q - m).toFloat
  let t ← time rounds m fun q => (BLAS.Float64.Mat.gemm (α q) A B 0.5 C).data[0]!
  let t' ← time rounds m fun q => (refGemm m.toUSize (α q) A.data B.data 0.5 C.data)[0]!
  let tb ← time rounds m fun q => (BLAS.Float64.Mat.gemmBlocked (α q) A B 0.5 C).data[0]!
  -- The same matrices as blocks of larger ones, with the leading dimension `m + 8`: they are
  -- packed, and the result is copied back into `C`'s array.
  let ld (X : BLAS.Float64.Mat m m) : BLAS.Float64.Mat m m :=
    (BLAS.Float64.Mat.ofLd? (vec ((m + 8) * m)) 0 (m + 8)).getD X
  let A₁ := ld A
  let B₁ := ld B
  let C₁ := ld C
  let tl ← time rounds m fun q => (BLAS.Float64.Mat.gemmBlocked (α q) A₁ B₁ 0.5 C₁).data[0]!
  return ([⟨s!"gemm {m}", t, some t'⟩, ⟨s!"gemmBlocked {m}", tb, some t'⟩,
    ⟨s!"gemmBlocked {m}, ld = {m} + 8 / ld = {m}", tl, some tb⟩], 2 * m * m * m)

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
  let gemm ← gemmSizes.mapM (gemmRows rounds)
  let rows := rows ++ (gemm.map (·.1)).flatten
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
    IO.println "\n`gemm` of square matrices, in GFLOP/s.\n"
    IO.println "| Size | gemm | gemmBlocked | gemmBlocked, ld = m + 8 | Reference |"
    IO.println "|--:|--:|--:|--:|--:|"
    for (rs, flops) in gemm, m in gemmSizes do
      let g (t : Float) := fmt (flops.toFloat / (t * 1e6))
      match rs with
      | [r, rb, rl] =>
        IO.println s!"| {m} | {g r.time} | {g rb.time} | {g rl.time} | {(r.ref.map g).getD "—"} |"
      | _ => pure ()
