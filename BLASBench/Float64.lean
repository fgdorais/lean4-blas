/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
import all BLAS.Internal
public import BLASBench.Basic

/-!
# Benchmarks of the `Float64` routines

The benchmarks of `lake exe bench`, with hand-written reference loops for comparison.
-/

open ScalarArray

namespace BLASBench.Float64

/-- A vector of `n` elements computed from their indices. -/
def vec (n : Nat) : Float64Array := .ofFn (n := n) fun i => (i.val % 7).toFloat - 3

/-- An index below `a.usize` is a valid index of `a`. -/
theorem lt_size_of_lt_usize {a : Float64Array} {i : USize} (h : i < a.usize) : i.toNat < a.size :=
  Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp h) a.toNat_usize_le

/-
The references are hand-written loops over `USize` indices bounded by `usize`, with unchecked reads
and writes, so that a ratio below 1 isn't due to a slow reference. They use scalar-arrays'
`Float64Array`, which has the lemmas on `usize` and `uset` that prove the indices valid.
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
      loop hs (z.uset i (α * x.uget i hx + z.uget i (by lia)) (by lia)) (by simp [hz]) (i + 1)
    else z

/-- The plane rotation of `x` and `y` by `c` and `s`. -/
partial def refRot (c s : Float) (x y : Float64Array) : Float64Array × Float64Array :=
  if hs : x.size = y.size then loop hs x y rfl rfl 0 else (x, y)
where
  /-- The loop from index `i`, over `a` and `b` of the sizes of `x` and `y`. -/
  loop (hs : x.size = y.size) (a b : Float64Array) (ha : a.size = x.size) (hb : b.size = y.size)
      (i : USize) : Float64Array × Float64Array :=
    if h : i < x.usize then
      have hx := lt_size_of_lt_usize h
      let u := a.uget i (by lia)
      let v := b.uget i (by lia)
      loop hs (a.uset i (c * u + s * v) (by lia)) (b.uset i (c * v - s * u) (by lia))
        (by simp [ha]) (by simp [hb]) (i + 1)
    else (a, b)

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
      loop hs (i + 1) (s + x.uget i hx * y.uget i (by lia))
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
  BLAS.toNat_mul_add_le (n := m.toNat) (USize.lt_iff_toNat_lt.mp hj)
    (by rw [h.ha]; exact Nat.le_refl _)

/-- The element `off + i` of a column at `off`, for `i < m`. -/
theorem idx_lt {m off i : USize} {p : Nat} (hw : off.toNat + m.toNat ≤ p) (hi : i < m) :
    (off + i).toNat < p :=
  ScalarArray.Notation.toNat_add_lt_of_window hw (USize.lt_iff_toNat_lt.mp hi)

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
  let rot ← time rounds n fun _ => Id.run do
    let mut z := (v, w)
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.rot 0.6 0.8 z.1 z.2
    return z.1.data[0]! + z.2.data[0]!
  let rot' ← time rounds n fun _ => Id.run do
    let mut z := (x, w.data)
    for _ in [0:reps] do
      z := refRot 0.6 0.8 z.1 z.2
    return z.1[0]! + z.2[0]!
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
  return [⟨s!"axpy ×{reps}", axpy, some axpy'⟩,
    ⟨s!"scal ×{reps}", scal, some scal'⟩, ⟨s!"copy ×{reps}", copy, none⟩,
    ⟨s!"rot ×{reps}", rot, some rot'⟩, ⟨"dot", dot, some dot'⟩, ⟨"asum", asum, some asum'⟩, ⟨"nrm2", nrm2, some nrm2'⟩,
    ⟨"iamax", iamax, some iamax'⟩, ⟨"iamax (increasing)", iamaxUp, some iamaxUp'⟩,
    ⟨s!"axpy ×{reps}, stride 2 / stride 1", axpy2, some axpy⟩,
    ⟨"dot, stride 2 / stride 1", dot2, some dot⟩]

/-- An `m × m` matrix computed from its indices. -/
def mat (m s : Nat) : BLAS.Float64.Mat m m :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat - 5

/--
The `gemm` benchmarks for `m × m` matrices: the rows of `gemmNaive` and `gemm`, and their
floating-point operations. Each timed call depends on its argument, which is `m`, so that the
compiler can't hoist it out of the timing loop.
-/
def gemmRows (rounds m : Nat) : IO (List Row × Nat) := do
  let A := mat m 1
  let B := mat m 2
  let C := mat m 3
  let α (q : Nat) := 1.5 + (q - m).toFloat
  let t ← time rounds m fun q => (BLAS.Float64.Mat.gemmNaive (α q) A B 0.5 C).data[0]!
  let t' ← time rounds m fun q => (refGemm m.toUSize (α q) A.data B.data 0.5 C.data)[0]!
  let tb ← time rounds m fun q => (BLAS.Float64.Mat.gemm (α q) A B 0.5 C).data[0]!
  -- The same matrices as blocks of larger ones, with the leading dimension `m + 8`: they are
  -- packed, and the result is copied back into `C`'s array.
  let ld (X : BLAS.Float64.Mat m m) : BLAS.Float64.Mat m m :=
    (BLAS.Float64.Mat.ofLd? (vec ((m + 8) * m)) 0 (m + 8)).getD X
  let A₁ := ld A
  let B₁ := ld B
  let C₁ := ld C
  let tl ← time rounds m fun q => (BLAS.Float64.Mat.gemm (α q) A₁ B₁ 0.5 C₁).data[0]!
  return ([⟨s!"gemmNaive {m}", t, some t'⟩, ⟨s!"gemm {m}", tb, some t'⟩,
    ⟨s!"gemm {m}, ld = {m} + 8 / ld = {m}", tl, some tb⟩], 2 * m * m * m)

/--
The Level 2 benchmarks for `m × m` matrices, ten calls per round: `gemv`, `gemvT` and `ger`, on
packed operands, `gemv` with `x` and `y` at stride 2, and `trsv` on both triangles. Each makes
`2 * m * m` floating-point operations per call, except `trsv`, which makes about `m * m`.
-/
def level2Rows (rounds m : Nat) : IO (List Row × Nat) := do
  let A := mat m 1
  let x : BLAS.Float64.Vec m := .ofArray (vec m) (by simp [vec])
  let x2 : BLAS.Float64.Vec m := (BLAS.Float64.Vec.ofStride? (vec (2 * m)) 0 2).getD x
  let α (q : Nat) := 1.5 + (q - m).toFloat
  let tv ← time rounds m fun q => Id.run do
    let mut y := x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.gemv (α q) A x 0.5 y
    return y.data[0]!
  let tt ← time rounds m fun q => Id.run do
    let mut y := x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.gemvT (α q) A x 0.5 y
    return y.data[0]!
  let tg ← time rounds m fun q => Id.run do
    let mut B := A
    for _ in [0:reps] do
      B := BLAS.Float64.Mat.ger (α q) x x B
    return B.data[0]!
  let tv2 ← time rounds m fun q => Id.run do
    let mut y := x2
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.gemv (α q) A x2 0.5 y
    return y.data[0]!
  let T : BLAS.Float64.Mat m m := .ofFn fun i j =>
    if i.val = j.val then (m + 4 + i.val).toFloat else ((i.val * 7 + j.val * 13) % 11).toFloat - 5
  let tl ← time rounds m fun q => Id.run do
    let mut y := BLAS.Float64.Vec.scal (α q) x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.trsv .lower .nonUnit T y
    return y.data[0]!
  let tu ← time rounds m fun q => Id.run do
    let mut y := BLAS.Float64.Vec.scal (α q) x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.trsv .upper .nonUnit T y
    return y.data[0]!
  return ([⟨s!"gemv {m} ×{reps}", tv, none⟩, ⟨s!"gemvT {m} ×{reps}", tt, none⟩,
    ⟨s!"ger {m} ×{reps}", tg, none⟩, ⟨s!"gemv {m} ×{reps}, stride 2 / stride 1", tv2, some tv⟩,
    ⟨s!"trsv lower {m} ×{reps}", tl, none⟩, ⟨s!"trsv upper {m} ×{reps}", tu, none⟩],
    2 * m * m * reps)

/-- All the benchmarks: Level 1, Level 2 and `gemm`, each with its floating-point operations. -/
public def all (rounds n : Nat) : IO (List Row × List (List Row × Nat) × List (List Row × Nat)) := do
  let rows ← rows rounds n
  let level2 ← level2Sizes.mapM (level2Rows rounds)
  let gemm ← gemmSizes.mapM (gemmRows rounds)
  return (rows, level2, gemm)

end BLASBench.Float64
