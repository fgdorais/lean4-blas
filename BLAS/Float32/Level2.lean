/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Level1
public import BLAS.Float32.Mat

/-!
# Level 2

Matrix-vector operations: the products `gemv` and `gemvT`, and the rank-one update `ger`. The
triangular solve `trsv` is in `BLAS.Float32.Trsv`.

Each routine computes every element with the operations of the reference BLAS, in the same order.
It runs loops over `USize` indices when its arrays' sizes fit in a `USize`, and its model
otherwise, so that its specification needs no hypothesis on the size. `gemv` and `gemvT` handle
four columns of `A` per loop, which doesn't change any element's operations.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {m n : Nat}

/-! ## `gemv` -/

/--
The value of the loops of `gemv` at the index `i` of `y`, from its old value `v`, on the arrays:
`betaMul β v`, plus the terms `α * x[j] * A[i, j]`.
-/
@[expose] public def gemvSumAt (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32) (i : Nat)
    (v : Float32) : Float32 :=
  Nat.fold n (fun j _ s => s + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!)
    (betaMul β v)

/--
The value of `gemv` at the index `i` of `y`, from its old value `v`, on the arrays, with the
special cases of the reference BLAS: `v` when `n = 0`, and `betaMul β v` when `α = 0`.
-/
@[expose] public def gemvAt (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32) (i : Nat)
    (v : Float32) : Float32 :=
  if n = 0 then v else if α == 0 then betaMul β v else gemvSumAt α A x β i v

/-- The step of `gemv` for column `j`: adds `α * x[j] * A[i, j]` to `y[i]`, in the array `c`. -/
@[expose] public def gemvCol (α : Float32) (A : Mat m n) (x : Vec n) (y : Vec m) (j : Nat)
    (c : Float32Array) : Float32Array :=
  c.modifyAt y.stride.idx 0 m fun i v =>
    v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!

/-- The sizes of the arrays of `gemv`, which fit in a `USize`. -/
@[expose] public def GemvFits (A : Mat m n) (x : Vec n) (y : Vec m) : Prop :=
  A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size

/-- `y.data` scaled by `β`, in place when it is not shared. -/
public def gemvScale (β : Float32) (y : Vec m) (hs : y.data.size < USize.size) : Float32Array :=
  have hmu : m.toUSize.toNat = m := y.toNat_toUSize hs
  let a := y.data
  let o := y.off.toUSize
  let c := y.inc.toUSize
  (inplace a do
    for i in 0...m.toUSize do
      have hk : (o + c * i).toNat < a.size := y.toNat_index_lt hs (by lia)
      a[o + c * i] := betaMul β a[o + c * i]).2

private theorem gemvScale_eq (β : Float32) (y : Vec m) (hs : y.data.size < USize.size) :
    gemvScale β y hs = y.data.modifyAt y.stride.idx 0 m fun _ v => betaMul β v := by
  unfold gemvScale
  have he := y.loop_idx hs
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v) (he := he)
    (hg := fun _ _ _ _ => rfl)]
  simp only [Tail.run_done, USize.toNat_zero, y.toNat_toUSize hs]

/--
Adds the columns `j` to `j + 3` of `gemv` to `y`'s elements in the array `c`, in one sweep over
the rows: `c[i] + t₀ * A[i, j] + … + t₃ * A[i, j + 3]`, from the left, with `tₗ = α * x[j + l]`.
It reads and writes each element of `y` once for four columns.
-/
public def gemvSweep4 (α : Float32) (A : Mat m n) (x : Vec n) (y : Vec m) (hs : GemvFits A x y)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc) (j : USize)
    (hj : j.toNat + 3 < n) (c : Float32Array) (hc : c.size = y.data.size) :
    {c' : Float32Array // c'.size = c.size} :=
  have hn : n < USize.size := by have := x.toNat_toUSize hs.2.1; grind
  have h₁ : (j + 1).toNat < n := by grind
  have h₂ : (j + 2).toNat < n := by grind
  have h₃ : (j + 3).toNat < n := by grind
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  let t₀ := α * x.uget xo xc rfl rfl hs.2.1 j (by lia)
  let t₁ := α * x.uget xo xc rfl rfl hs.2.1 (j + 1) h₁
  let t₂ := α * x.uget xo xc rfl rfl hs.2.1 (j + 2) h₂
  let t₃ := α * x.uget xo xc rfl rfl hs.2.1 (j + 3) h₃
  have hmu : m.toUSize.toNat = m := y.toNat_toUSize hs.2.2
  inplace c do
    for i in 0...m.toUSize do
      have hk : (o + cc * i).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      have hi : i.toNat < m := by lia
      c[o + cc * i] := c[o + cc * i] + t₀ * A.uget ao al rfl rfl hs.1 i j hi (by lia) +
        t₁ * A.uget ao al rfl rfl hs.1 i (j + 1) hi h₁ +
        t₂ * A.uget ao al rfl rfl hs.1 i (j + 2) hi h₂ +
        t₃ * A.uget ao al rfl rfl hs.1 i (j + 3) hi h₃
  then fun _ c' h => ⟨c', h⟩

/-- `gemvSweep4` for one column `j`. -/
public def gemvSweep1 (α : Float32) (A : Mat m n) (x : Vec n) (y : Vec m) (hs : GemvFits A x y)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc) (j : USize)
    (hj : j.toNat < n) (c : Float32Array) (hc : c.size = y.data.size) :
    {c' : Float32Array // c'.size = c.size} :=
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  let t := α * x.uget x.off.toUSize x.inc.toUSize rfl rfl hs.2.1 j hj
  have hmu : m.toUSize.toNat = m := y.toNat_toUSize hs.2.2
  inplace c do
    for i in 0...m.toUSize do
      have hk : (o + cc * i).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      c[o + cc * i] := c[o + cc * i] + t * A.uget ao al rfl rfl hs.1 i j (by lia) hj
  then fun _ c' h => ⟨c', h⟩

private theorem gemvSweep4_eq (α : Float32) (A : Mat m n) (x : Vec n) (y : Vec m)
    (hs : GemvFits A x y) (o cc : USize)
    (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc) (j : USize) (hj : j.toNat + 3 < n)
    (c : Float32Array) (hc : c.size = y.data.size) :
    (gemvSweep4 α A x y hs o cc ho hcc j hj c hc).1 = gemvCol α A x y (j.toNat + 3)
      (gemvCol α A x y (j.toNat + 2)
        (gemvCol α A x y (j.toNat + 1) (gemvCol α A x y j.toNat c))) := by
  have hn : n < USize.size := by have := x.toNat_toUSize hs.2.1; grind
  have h₁ : (j + 1).toNat = j.toNat + 1 := by grind
  have h₂ : (j + 2).toNat = j.toNat + 2 := by grind
  have h₃ : (j + 3).toNat = j.toNat + 3 := by grind
  have he := y.loop_idx hs.2.2
  have hinj := y.fits.injOn (lo := 0) (Nat.le_refl _)
  have hmu := y.toNat_toUSize hs.2.2
  subst ho hcc
  unfold gemvSweep4
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_modify (G := fun i v =>
      v + α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + i]! +
        α * x.data[x.off + x.inc * (j.toNat + 1)]! * A.data[A.off + A.ld * (j.toNat + 1) + i]! +
        α * x.data[x.off + x.inc * (j.toNat + 2)]! * A.data[A.off + A.ld * (j.toNat + 2) + i]! +
        α * x.data[x.off + x.inc * (j.toNat + 3)]! * A.data[A.off + A.ld * (j.toNat + 3) + i]!)
    (he := he)]
  · simp only [Tail.run_done, USize.toNat_zero, hmu]
    simp only [gemvCol, modifyAt_modifyAt _ _ hinj]
  · intro i _ hi v
    rw [hmu] at hi
    simp only [Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def, h₁, h₂, h₃]
    rw [getElem!_pos x.data _ (x.index_lt (by lia : j.toNat < n)),
      getElem!_pos x.data _ (x.index_lt (by lia : j.toNat + 1 < n)),
      getElem!_pos x.data _ (x.index_lt (by lia : j.toNat + 2 < n)),
      getElem!_pos x.data _ (x.index_lt (by lia : j.toNat + 3 < n)),
      getElem!_pos A.data _ (A.index_lt hi (by lia : j.toNat < n)),
      getElem!_pos A.data _ (A.index_lt hi (by lia : j.toNat + 1 < n)),
      getElem!_pos A.data _ (A.index_lt hi (by lia : j.toNat + 2 < n)),
      getElem!_pos A.data _ (A.index_lt hi (by lia : j.toNat + 3 < n))]

private theorem gemvSweep1_eq (α : Float32) (A : Mat m n) (x : Vec n) (y : Vec m)
    (hs : GemvFits A x y) (o cc : USize)
    (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc) (j : USize) (hj : j.toNat < n)
    (c : Float32Array) (hc : c.size = y.data.size) :
    (gemvSweep1 α A x y hs o cc ho hcc j hj c hc).1 = gemvCol α A x y j.toNat c := by
  have he := y.loop_idx hs.2.2
  have hmu := y.toNat_toUSize hs.2.2
  subst ho hcc
  unfold gemvSweep1
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_modify (G := fun i v =>
      v + α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + i]!) (he := he)]
  · simp only [Tail.run_done, USize.toNat_zero, hmu, gemvCol]
  · intro i _ hi v
    rw [hmu] at hi
    rw [Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def,
      getElem!_pos x.data _ (x.index_lt hj), getElem!_pos A.data _ (A.index_lt hi hj)]

/--
The columns `j` to `n - 1` of `gemv`, added to `y`'s elements in the array `c`: four at a time by
`gemvSweep4`, then one at a time by `gemvSweep1`.
-/
public def gemvCols (α : Float32) (A : Mat m n) (x : Vec n) (y : Vec m) (hs : GemvFits A x y)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc) (j : USize)
    (hj : j.toNat ≤ n) (c : Float32Array) (hc : c.size = y.data.size) :
    Float32Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  if h4 : 4 ≤ n.toUSize - j then
    have h4' : j.toNat + 3 < n := by grind
    let c' := gemvSweep4 α A x y hs o cc ho hcc j h4' c hc
    gemvCols α A x y hs o cc ho hcc (j + 4) (by grind) c'.1 (c'.2.trans hc)
  else if h1 : j < n.toUSize then
    have h1' : j.toNat < n := by grind
    let c' := gemvSweep1 α A x y hs o cc ho hcc j h1' c hc
    gemvCols α A x y hs o cc ho hcc (j + 1) (by grind) c'.1 (c'.2.trans hc)
  else c
termination_by n - j.toNat
decreasing_by all_goals grind

private theorem gemvCols_eq (α : Float32) (A : Mat m n) (x : Vec n) (y : Vec m)
    (hs : GemvFits A x y) (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (j : USize) (hj : j.toNat ≤ n) (c : Float32Array) (hc : c.size = y.data.size) :
    gemvCols α A x y hs o cc ho hcc j hj c hc = iterRange (gemvCol α A x y) j.toNat n c := by
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  obtain ⟨d, hd⟩ : ∃ d, n - j.toNat = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing j c with
  | ind d ih =>
    rw [gemvCols]
    split
    · rename_i h4
      have h4' : j.toNat + 3 < n := by grind
      have hj4 : (j + 4).toNat = j.toNat + 4 := by grind
      rw [ih (n - (j + 4).toNat) (by lia) (j + 4) _ _ _ rfl, gemvSweep4_eq, hj4,
        iterRange_of_lt _ (by lia : j.toNat < n), iterRange_of_lt _ (by lia : j.toNat + 1 < n),
        iterRange_of_lt _ (by lia : j.toNat + 1 + 1 < n),
        iterRange_of_lt _ (by lia : j.toNat + 1 + 1 + 1 < n)]
    · split
      · rename_i h4 h1
        have h1' : j.toNat < n := by grind
        have hj1 : (j + 1).toNat = j.toNat + 1 := by grind
        rw [ih (n - (j + 1).toNat) (by lia) (j + 1) _ _ _ rfl, gemvSweep1_eq, hj1,
          iterRange_of_lt _ h1']
      · rename_i h4 h1
        rw [iterRange_of_le _ (by grind)]

/-- The array of `gemv`. -/
public def gemvData (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32) (y : Vec m) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    gemvCols α A x y hs y.off.toUSize y.inc.toUSize rfl rfl 0 (by simp) (gemvScale β y hs.2.2)
      (by rw [gemvScale_eq, size_modifyAt])
  else y.data.modifyAt y.stride.idx 0 m (gemvSumAt α A x β)

public theorem gemvData_eq (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32) (y : Vec m) :
    gemvData α A x β y = y.data.modifyAt y.stride.idx 0 m (gemvSumAt α A x β) := by
  unfold gemvData
  split
  · rename_i hs
    have hinj := y.fits.injOn (lo := 0) (Nat.le_refl _)
    rw [gemvCols_eq α A x y hs _ _ rfl rfl, gemvScale_eq]
    simp only [USize.toNat_zero]
    rw [show gemvCol α A x y = fun j c => c.modifyAt y.stride.idx 0 m fun i v =>
        v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]! from rfl,
      iterRange_modifyAt _ _ hinj, modifyAt_modifyAt _ _ hinj]
    rfl
  · rfl

/--
`gemv α A x β y` is `α * A * x + β * y`, with the operations of the reference BLAS, in its order
for each element: it scales `y` by `β`, then adds `α * x[j]` times column `j` of `A`, for
`j = 0, …, n - 1`. It adds four columns in each pass over `y`, which gives the same result with a
quarter of the reads and writes of `y`. As in the reference BLAS, it returns `y` when `n = 0`, sets
`y` to `0` without reading it when `β = 0`, and only scales `y` when `α = 0`, without reading `A`
or `x`. It updates `y` in place when its array is not shared, and leaves the elements of the array
outside `y` unchanged.
-/
@[expose] public def gemv (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32) (y : Vec m) :
    Vec m :=
  if n = 0 then y
  else if α == 0 then
    { data := y.scalBetaData β
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [Vec.scalBetaData_eq, size_modifyAt]; exact y.bound }
  else
    { data := gemvData α A x β y
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [gemvData_eq, size_modifyAt]; exact y.bound }

/-- The array of `gemv α A x β y` is the array of `y` with its elements updated. -/
public theorem data_gemv (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32) (y : Vec m) :
    (gemv α A x β y).data = y.data.modifyAt y.stride.idx 0 m (gemvAt α A x β) := by
  unfold gemv
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte]
    rw [modifyAt_congr_fun _ _ (g' := fun _ v => v) (fun i v _ _ => by simp [gemvAt, hn]),
      modifyAt_id]
  · simp only [hn, ↓reduceIte]
    cases hα : α == 0
    · simp only [Bool.false_eq_true, ↓reduceIte, gemvData_eq]
      exact modifyAt_congr_fun _ _ fun i v _ _ => by simp [gemvAt, hn, hα]
    · simp only [↓reduceIte, Vec.scalBetaData_eq]
      exact modifyAt_congr_fun _ _ fun i v _ _ => by simp [gemvAt, hn, hα]

@[simp] public theorem off_gemv (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32) (y : Vec m) :
    (gemv α A x β y).off = y.off := by
  unfold gemv; split <;> (try split) <;> rfl

@[simp] public theorem inc_gemv (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32) (y : Vec m) :
    (gemv α A x β y).inc = y.inc := by
  unfold gemv; split <;> (try split) <;> rfl

/--
Element `i` of `gemv α A x β y` is `y[i]` when `n = 0`, `betaMul β y[i]` when `α = 0`, and
otherwise `betaMul β y[i]`, plus the terms `α * x[j] * A[i, j]` for `j = 0, …, n - 1`, added from
the left.
-/
@[simp] public theorem getElem_gemv (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32)
    (y : Vec m) (i : Nat) (h : i < m) :
    (gemv α A x β y)[i] =
      if n = 0 then y[i] else if α == 0 then betaMul β y[i]
      else Nat.fold n (fun j _ s => s + α * x[j] * A[(i, j)]) (betaMul β y[i]) := by
  rw [Vec.getElem_of_data_eq_modifyAt _ (data_gemv α A x β y) (off_gemv α A x β y)
    (inc_gemv α A x β y) i h, gemvAt, gemvSumAt]
  congr
  funext j hj s
  rw [getElem!_pos x.data _ (x.index_lt hj), getElem!_pos A.data _ (A.index_lt h hj)]
  rfl

/-! ## `gemvT` -/

/--
The value of the loops of `gemvT` at the index `j` of `y`, from its old value `v`, on the arrays:
`betaMul β v + α * s`, where `s` sums the terms `A[i, j] * x[i]`.
-/
@[expose] public def gemvTSumAt (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32) (j : Nat)
    (v : Float32) : Float32 :=
  betaMul β v + α * Nat.fold m
    (fun i _ s => s + A.data[A.off + A.ld * j + i]! * x.data[x.off + x.inc * i]!) 0

/--
The value of `gemvT` at the index `j` of `y`, from its old value `v`, on the arrays, with the
special cases of the reference BLAS: `v` when `m = 0`, and `betaMul β v` when `α = 0`.
-/
@[expose] public def gemvTAt (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32) (j : Nat)
    (v : Float32) : Float32 :=
  if m = 0 then v else if α == 0 then betaMul β v else gemvTSumAt α A x β j v

/-- The sum of the products `A[i, j] * x[i]` of column `j` of `A` and `x`, from the left. -/
@[expose] public def gemvTSum (A : Mat m n) (x : Vec m) (j : Nat) : Float32 :=
  Nat.fold m (fun i _ s => s + A.data[A.off + A.ld * j + i]! * x.data[x.off + x.inc * i]!) 0

/--
The loop of `gemvTSums4` from the index `i`, up to the bound `mu`, which is `m`: the sums `s₀`,
`s₁`, `s₂` and `s₃` of the columns `j` to `j + 3`, so far. At the end, it pushes them onto `acc`.
The four sums are independent, so that their additions overlap, and they share the reads of `x`.
-/
public def gemvTSums4 (A : Mat m n) (x : Vec m) (ao al xo xc : USize) (ha : A.off.toUSize = ao)
    (hl : A.ld.toUSize = al) (hx : x.off.toUSize = xo) (hc : x.inc.toUSize = xc)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size) (hn : n < USize.size)
    (mu : USize) (hmu : mu.toNat = m) (j : USize) (hj : j.toNat + 3 < n) (acc : Float32Array)
    (i : USize) (s₀ s₁ s₂ s₃ : Float32) : Float32Array :=
  if hi : i < mu then
    have hi' : i.toNat < m := hmu ▸ hi
    have h₁ : (j + 1).toNat < n := by grind
    have h₂ : (j + 2).toNat < n := by grind
    have h₃ : (j + 3).toNat < n := by grind
    let xi := x.uget xo xc hx hc hs.2 i hi'
    gemvTSums4 A x ao al xo xc ha hl hx hc hs hn mu hmu j hj acc (i + 1)
      (s₀ + A.uget ao al ha hl hs.1 i j hi' (by lia) * xi)
      (s₁ + A.uget ao al ha hl hs.1 i (j + 1) hi' h₁ * xi)
      (s₂ + A.uget ao al ha hl hs.1 i (j + 2) hi' h₂ * xi)
      (s₃ + A.uget ao al ha hl hs.1 i (j + 3) hi' h₃ * xi)
  else (((acc.push s₀).push s₁).push s₂).push s₃
termination_by mu.toNat - i.toNat
decreasing_by grind

/-- A step of a column sum, on `USize` indices, is the step of `gemvTSum`. -/
private theorem gemvTSum_step (A : Mat m n) (x : Vec m) (ao al xo xc : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hx : x.off.toUSize = xo)
    (hc : x.inc.toUSize = xc) (hs : A.data.size < USize.size ∧ x.data.size < USize.size)
    (i j : USize) (hi : i.toNat < m) (hj : j.toNat < n) :
    A.uget ao al ha hl hs.1 i j hi hj * x.uget xo xc hx hc hs.2 i hi =
      A.data[A.off + A.ld * j.toNat + i.toNat]! * x.data[x.off + x.inc * i.toNat]! := by
  rw [Mat.uget_eq_getElem, Vec.uget_eq_getElem, getElem!_pos A.data _ (A.index_lt hi hj),
    getElem!_pos x.data _ (x.index_lt hi)]
  rfl

private theorem gemvTSums4_eq (A : Mat m n) (x : Vec m) (ao al xo xc : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hx : x.off.toUSize = xo)
    (hc : x.inc.toUSize = xc) (hs : A.data.size < USize.size ∧ x.data.size < USize.size)
    (hn : n < USize.size) (mu : USize) (hmu : mu.toNat = m) (j : USize) (hj : j.toNat + 3 < n)
    (acc : Float32Array) (i : USize) (k : Nat) (hk : i.toNat = k) (hkm : k ≤ m) :
    gemvTSums4 A x ao al xo xc ha hl hx hc hs hn mu hmu j hj acc i
      (Nat.fold k (fun i _ s => s + A.data[A.off + A.ld * j.toNat + i]! *
        x.data[x.off + x.inc * i]!) 0)
      (Nat.fold k (fun i _ s => s + A.data[A.off + A.ld * (j.toNat + 1) + i]! *
        x.data[x.off + x.inc * i]!) 0)
      (Nat.fold k (fun i _ s => s + A.data[A.off + A.ld * (j.toNat + 2) + i]! *
        x.data[x.off + x.inc * i]!) 0)
      (Nat.fold k (fun i _ s => s + A.data[A.off + A.ld * (j.toNat + 3) + i]! *
        x.data[x.off + x.inc * i]!) 0) =
      (((acc.push (gemvTSum A x j.toNat)).push (gemvTSum A x (j.toNat + 1))).push
        (gemvTSum A x (j.toNat + 2))).push (gemvTSum A x (j.toNat + 3)) := by
  have h₁ : (j + 1).toNat = j.toNat + 1 := by grind
  have h₂ : (j + 2).toNat = j.toNat + 2 := by grind
  have h₃ : (j + 3).toNat = j.toNat + 3 := by grind
  obtain ⟨d, hd⟩ : ∃ d, m - k = d := ⟨_, rfl⟩
  induction d generalizing i k with
  | zero =>
    rw [gemvTSums4, dite_eq_right_of_eq_false (eq_false (by rw [USize.lt_iff_toNat_lt]; lia))]
    obtain rfl : k = m := by lia
    rfl
  | succ d ih =>
    have hi : i < mu := USize.lt_iff_toNat_lt.mpr (by lia)
    have hi' : i.toNat < m := by lia
    have hsucc : (i + 1).toNat = k + 1 := by clear ih; grind
    rw [gemvTSums4, dite_eq_left_of_eq_true (eq_true hi)]
    simp only []
    rw [gemvTSum_step A x ao al xo xc ha hl hx hc hs, gemvTSum_step A x ao al xo xc ha hl hx hc hs,
      gemvTSum_step A x ao al xo xc ha hl hx hc hs, gemvTSum_step A x ao al xo xc ha hl hx hc hs,
      h₁, h₂, h₃]
    have := ih (i + 1) (k + 1) hsucc (by lia) (by lia)
    simp only [Nat.fold_succ] at this
    subst hk
    exact this

/--
The sums of the columns `j` to `n - 1` of `A` with `x`, pushed onto `acc`: four columns at a time
by `gemvTSums4`, then one at a time.
-/
public def gemvTSums (A : Mat m n) (x : Vec m) (ao al xo xc : USize) (ha : A.off.toUSize = ao)
    (hl : A.ld.toUSize = al) (hx : x.off.toUSize = xo) (hc : x.inc.toUSize = xc)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size) (hn : n < USize.size)
    (mu : USize) (hmu : mu.toNat = m) (nu : USize) (hnu : nu.toNat = n) (j : USize)
    (hj : j.toNat ≤ n) (acc : Float32Array) : Float32Array :=
  if h4 : 4 ≤ nu - j then
    have h4' : j.toNat + 3 < n := by grind
    gemvTSums A x ao al xo xc ha hl hx hc hs hn mu hmu nu hnu (j + 4) (by grind)
      (gemvTSums4 A x ao al xo xc ha hl hx hc hs hn mu hmu j h4' acc 0 0 0 0 0)
  else if h1 : j < nu then
    have h1' : j.toNat < n := by grind
    gemvTSums A x ao al xo xc ha hl hx hc hs hn mu hmu nu hnu (j + 1) (by grind)
      (acc.push (foldUpTo m
        (fun i _ s => s + A.data[A.off + A.ld * j.toNat + i]! * x.data[x.off + x.inc * i]!)
        (fun i hi s => s + A.uget ao al ha hl hs.1 i j hi h1' * x.uget xo xc hx hc hs.2 i hi) 0))
  else acc
termination_by n - j.toNat
decreasing_by all_goals grind

public theorem gemvTSums_spec (A : Mat m n) (x : Vec m) (ao al xo xc : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hx : x.off.toUSize = xo)
    (hc : x.inc.toUSize = xc) (hs : A.data.size < USize.size ∧ x.data.size < USize.size)
    (hn : n < USize.size) (mu : USize) (hmu : mu.toNat = m) (nu : USize) (hnu : nu.toNat = n)
    (j : USize) (hj : j.toNat ≤ n) (acc : Float32Array) (hacc : acc.size = j.toNat)
    (hv : ∀ q (h : q < acc.size), acc[q] = gemvTSum A x q) :
    let s := gemvTSums A x ao al xo xc ha hl hx hc hs hn mu hmu nu hnu j hj acc
    s.size = n ∧ ∀ q (h : q < s.size), s[q] = gemvTSum A x q := by
  obtain ⟨d, hd⟩ : ∃ d, n - j.toNat = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing j acc with
  | ind d ih =>
    rw [gemvTSums]
    split
    · rename_i h4
      have h4' : j.toNat + 3 < n := by grind
      have hj4 : (j + 4).toNat = j.toNat + 4 := by grind
      have e := gemvTSums4_eq A x ao al xo xc ha hl hx hc hs hn mu hmu j h4' acc 0 0 (by simp)
        (by lia)
      simp only [Nat.fold_zero] at e
      refine ih (n - (j + 4).toNat) (by lia) (j + 4) _ _ ?_ ?_ rfl
      · rw [e]; simp only [size_push]; lia
      · rw [e]
        intro q h
        simp only [getElem_push]
        split
        · split
          · split
            · split
              · exact hv q _
              · have : q = j.toNat := by simp only [size_push] at *; lia
                subst this; rfl
            · have : q = j.toNat + 1 := by simp only [size_push] at *; lia
              subst this; rfl
          · have : q = j.toNat + 2 := by simp only [size_push] at *; lia
            subst this; rfl
        · have : q = j.toNat + 3 := by simp only [size_push] at *; lia
          subst this; rfl
    · split
      · rename_i h4 h1
        have h1' : j.toNat < n := by grind
        have hj1 : (j + 1).toNat = j.toNat + 1 := by grind
        refine ih (n - (j + 1).toNat) (by lia) (j + 1) _ _ ?_ ?_ rfl
        · simp only [size_push]; lia
        · intro q h
          simp only [getElem_push]
          split
          · exact hv q _
          · have : q = j.toNat := by simp only [size_push] at *; lia
            subst this
            rw [foldUpTo_eq _ _ _ (fun i hi s => by
              rw [gemvTSum_step A x ao al xo xc ha hl hx hc hs]) 0]
            rfl
      · rename_i h4 h1
        have : j.toNat = n := by grind
        exact ⟨by lia, hv⟩

/-- The array of `gemvT`. -/
public def gemvTData (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32) (y : Vec n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2.2
    have hn : n < USize.size := by grind
    let mu := m.toUSize
    have hmu : mu.toNat = m := x.toNat_toUSize hs.2.1
    let sums := gemvTSums A x _ _ _ _ rfl rfl rfl rfl ⟨hs.1, hs.2.1⟩ hn mu hmu nu hnu 0
      (by simp) (Float32Array.emptyWithCapacity n)
    have hsums : sums.size = n :=
      (gemvTSums_spec A x _ _ _ _ rfl rfl rfl rfl ⟨hs.1, hs.2.1⟩ hn mu hmu nu hnu 0 (by simp)
        (Float32Array.emptyWithCapacity n) (by simp) (by simp)).1
    let a := y.data
    let o := y.off.toUSize
    let c := y.inc.toUSize
    (inplace a do
      for j in 0...nu do
        have hk : (o + c * j).toNat < a.size := y.toNat_index_lt hs.2.2 (by lia)
        a[o + c * j] := betaMul β a[o + c * j] + α * sums.uget j (by lia)).2
  else y.data.modifyAt y.stride.idx 0 n (gemvTSumAt α A x β)

public theorem gemvTData_eq (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32) (y : Vec n) :
    gemvTData α A x β y = y.data.modifyAt y.stride.idx 0 n (gemvTSumAt α A x β) := by
  unfold gemvTData
  split
  · rename_i hs
    have he := y.loop_idx hs.2.2
    have hnu := y.toNat_toUSize hs.2.2
    have hspec := gemvTSums_spec A x _ _ _ _ rfl rfl rfl rfl ⟨hs.1, hs.2.1⟩ (by grind)
      m.toUSize (x.toNat_toUSize hs.2.1) n.toUSize hnu 0 (by simp)
      (Float32Array.emptyWithCapacity n) (by simp) (by simp)
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := gemvTSumAt α A x β) (he := he)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj v
      rw [hnu] at hj
      rw [Float32Array.uget_eq_getElem, hspec.2]
      rfl
  · rfl

/--
`gemvT α A x β y` is `α * Aᵀ * x + β * y`, with the operations of the reference BLAS, in its order
for each element: for each `j`, it sums the products `A[i, j] * x[i]` of column `j` of `A` and `x`
from the left, and adds `α` times the sum to `β * y[j]`. It computes the sums of four columns in
each pass over `x`, which gives the same sums and lets their additions overlap. As in the reference
BLAS, it returns `y` when `m = 0`, sets `y[j]` to `0` without reading it before adding the sum when
`β = 0`, and only scales `y` when `α = 0`, without reading `A` or `x`. It updates `y` in place when
its array is not shared, and leaves the elements of the array outside `y` unchanged.
-/
@[expose] public def gemvT (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32) (y : Vec n) :
    Vec n :=
  if m = 0 then y
  else if α == 0 then
    { data := y.scalBetaData β
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [Vec.scalBetaData_eq, size_modifyAt]; exact y.bound }
  else
    { data := gemvTData α A x β y
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [gemvTData_eq, size_modifyAt]; exact y.bound }

/-- The array of `gemvT α A x β y` is the array of `y` with its elements updated. -/
public theorem data_gemvT (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32) (y : Vec n) :
    (gemvT α A x β y).data = y.data.modifyAt y.stride.idx 0 n (gemvTAt α A x β) := by
  unfold gemvT
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte]
    rw [modifyAt_congr_fun _ _ (g' := fun _ v => v) (fun i v _ _ => by simp [gemvTAt, hm]),
      modifyAt_id]
  · simp only [hm, ↓reduceIte]
    cases hα : α == 0
    · simp only [Bool.false_eq_true, ↓reduceIte, gemvTData_eq]
      exact modifyAt_congr_fun _ _ fun i v _ _ => by simp [gemvTAt, hm, hα]
    · simp only [↓reduceIte, Vec.scalBetaData_eq]
      exact modifyAt_congr_fun _ _ fun i v _ _ => by simp [gemvTAt, hm, hα]

@[simp] public theorem off_gemvT (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32) (y : Vec n) :
    (gemvT α A x β y).off = y.off := by
  unfold gemvT; split <;> (try split) <;> rfl

@[simp] public theorem inc_gemvT (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32) (y : Vec n) :
    (gemvT α A x β y).inc = y.inc := by
  unfold gemvT; split <;> (try split) <;> rfl

/--
Element `j` of `gemvT α A x β y` is `y[j]` when `m = 0`, `betaMul β y[j]` when `α = 0`, and
otherwise `betaMul β y[j] + α * s`, where `s` sums the terms `A[i, j] * x[i]` for
`i = 0, …, m - 1` from the left, starting at `0`.
-/
@[simp] public theorem getElem_gemvT (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32)
    (y : Vec n) (j : Nat) (h : j < n) :
    (gemvT α A x β y)[j] =
      if m = 0 then y[j] else if α == 0 then betaMul β y[j]
      else betaMul β y[j] + α * Nat.fold m (fun i _ s => s + A[(i, j)] * x[i]) 0 := by
  rw [Vec.getElem_of_data_eq_modifyAt _ (data_gemvT α A x β y) (off_gemvT α A x β y)
    (inc_gemvT α A x β y) j h, gemvTAt, gemvTSumAt]
  congr
  funext i hi s
  rw [getElem!_pos x.data _ (x.index_lt hi), getElem!_pos A.data _ (A.index_lt hi h)]
  rfl

/-! ## `ger` -/

/--
The value of the loops of `ger` at `(i, j)`, from its old value `v`, on the arrays: `v` when
`y[j] = 0`, as the reference BLAS skips that column.
-/
@[expose] public def gerAt (α : Float32) (x : Vec m) (y : Vec n) (i j : Nat)
    (v : Float32) : Float32 :=
  if y.data[y.off + y.inc * j]! == 0 then v
  else v + x.data[x.off + x.inc * i]! * (α * y.data[y.off + y.inc * j]!)

/--
The number of rows that the loop of `ger` updates in a column: `0` when `y[j] = 0`. It is not
inlined, so that the column loop has a single call site, which the C compiler inlines and
vectorizes.
-/
@[noinline, expose] public def gerRows (mu : USize) (yj : Float32) : USize :=
  if yj == 0 then 0 else mu

public theorem gerRows_le {mu : USize} (hmu : mu.toNat = m) (yj : Float32) :
    (gerRows mu yj).toNat ≤ m := by
  unfold gerRows; split <;> simp [hmu]

/-- The array of `ger`. -/
public def gerData (α : Float32) (x : Vec m) (y : Vec n) (A : Mat m n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := x.toNat_toUSize hs.2.1
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2.2
    let a := A.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    let yo := y.off.toUSize
    let yc := y.inc.toUSize
    (inplace a do
      for j in 0...nu do
        let yj := y.uget yo yc rfl rfl hs.2.2 j (by lia)
        let t := α * yj
        let cj := ao + al * j
        -- The column is skipped by an empty loop: an `unless` would allocate a closure per column.
        let hi := gerRows mu yj
        have hhi : hi.toNat ≤ m := gerRows_le hmu yj
        for i in 0...hi do
          have hk : (cj + 1 * i).toNat < a.size := A.toNat_col_index_lt hs.1 (by lia) (by lia)
          a[cj + 1 * i] := a[cj + 1 * i] + x.uget xo xc rfl rfl hs.2.1 i (by lia) * t).2
  else mapMat A.data A.off A.ld m 0 n (gerAt α x y)

public theorem gerData_eq (α : Float32) (x : Vec m) (y : Vec n) (A : Mat m n) :
    gerData α x y A = mapMat A.data A.off A.ld m 0 n (gerAt α x y) := by
  unfold gerData
  split
  · rename_i hs
    have hmu := x.toNat_toUSize hs.2.1
    have hnu := y.toNat_toUSize hs.2.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (A.off + A.ld * j) 1).idx 0 m fun i v => gerAt α x y i j v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ A.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hy := getElem!_pos y.data (y.off + y.inc * j.toNat) (y.index_lt hj)
      rw [Tail.run_forInFrom_modify (G := fun i v => gerAt α x y i j.toNat v)
        (idx := (Stride.mk (A.off + A.ld * j.toNat) 1).idx)
        (he := fun i _ hi => A.toNat_col_index hs.1 (Nat.lt_of_lt_of_le hi
          (gerRows_le hmu _)) hj)]
      · apply run_congr
        simp only [USize.toNat_zero, gerRows, Vec.uget_eq_getElem, Vec.getElem_def, ← hy]
        split
        next h0 =>
          rw [USize.toNat_zero, modifyAt_of_le _ _ (Nat.le_refl _),
            modifyAt_congr_fun _ _ (g' := fun _ v => v) (fun i v _ _ => by simp [gerAt, h0]),
            modifyAt_id]
        next => rw [hmu]
      · intro i _ hi v
        have hi' : i.toNat < m := Nat.lt_of_lt_of_le hi (gerRows_le hmu _)
        simp only [gerRows, Vec.uget_eq_getElem, Vec.getElem_def, ← hy] at hi ⊢
        split at hi
        next => simp at hi
        next h0 =>
          rw [gerAt, getElem!_pos x.data (x.off + x.inc * i.toNat) (x.index_lt hi')]
          simp [h0]
  · rfl

/--
`ger α x y A` is `α * x * yᵀ + A`, by the loops of the reference BLAS: for each column `j`, it
adds `x` times `α * y[j]`. As in the reference BLAS, it returns `A` when `α = 0`, and skips the
columns with `y[j] = 0`, without reading `x`, so an infinity or a `NaN` in `x` doesn't reach
them. It updates `A` in place when its array is not shared, and leaves the elements of the array
outside `A` unchanged.
-/
@[expose] public def ger (α : Float32) (x : Vec m) (y : Vec n) (A : Mat m n) : Mat m n :=
  if α == 0 then A
  else
    { data := gerData α x y A
      off := A.off
      ld := A.ld
      le_ld := A.le_ld
      bound := by rw [gerData_eq, size_mapMat]; exact A.bound }

/-- The array of `ger α x y A` is the array of `A` with its elements updated. -/
public theorem data_ger (α : Float32) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).data =
      mapMat A.data A.off A.ld m 0 n fun i j v => if α == 0 then v else gerAt α x y i j v := by
  unfold ger
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, gerData_eq]
  · simp only [↓reduceIte, mapMat_id]

@[simp] public theorem off_ger (α : Float32) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).off = A.off := by
  unfold ger; split <;> rfl

@[simp] public theorem ld_ger (α : Float32) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).ld = A.ld := by
  unfold ger; split <;> rfl

/--
Element `(i, j)` of `ger α x y A` is `A[i, j]` when `α = 0` or `y[j] = 0`, and
`A[i, j] + x[i] * (α * y[j])` otherwise.
-/
@[simp] public theorem getElem_ger (α : Float32) (x : Vec m) (y : Vec n) (A : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (ger α x y A)[(i, j)] =
      if α == 0 || y[j] == 0 then A[(i, j)] else A[(i, j)] + x[i] * (α * y[j]) := by
  rw [getElem_of_data_eq_mapMat _ (data_ger α x y A) (off_ger α x y A) (ld_ger α x y A) i j h,
    gerAt,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt h.1),
    getElem!_pos y.data (y.off + y.inc * j) (y.index_lt h.2)]
  cases α == 0 <;> rfl

end Mat

end BLAS.Float32
