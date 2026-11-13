/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Level1
public import BLAS.Float64.Mat

/-!
# Level 2

Matrix-vector operations: the products `gemv` and `gemvT`, and the rank-one update `ger`. The
triangular solve `trsv` is in `BLAS.Float64.Trsv`.

Each routine runs the loops of the reference BLAS over `USize` indices when its arrays' sizes fit
in a `USize`, and its model otherwise, so that its specification needs no hypothesis on the size.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {m n : Nat}

/-! ## `gemv` -/

/--
The value of the loops of `gemv` at the index `i` of `y`, from its old value `v`, on the arrays:
`betaMul β v`, plus the terms `α * x[j] * A[i, j]`.
-/
@[expose] public def gemvSumAt (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (i : Nat)
    (v : Float) : Float :=
  Nat.fold n (fun j _ s => s + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!)
    (betaMul β v)

/--
The value of `gemv` at the index `i` of `y`, from its old value `v`, on the arrays, with the
special cases of the reference BLAS: `v` when `n = 0`, and `betaMul β v` when `α = 0`.
-/
@[expose] public def gemvAt (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (i : Nat)
    (v : Float) : Float :=
  if n = 0 then v else if α == 0 then betaMul β v else gemvSumAt α A x β i v

/-- The array of `gemv`. -/
public def gemvData (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
    Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := y.toNat_toUSize hs.2.2
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2.1
    let a := y.data
    let o := y.off.toUSize
    let c := y.inc.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    (inplace a do
      for i in 0...mu do
        have hk : (o + c * i).toNat < a.size := y.toNat_index_lt hs.2.2 (by lia)
        a[o + c * i] := betaMul β a[o + c * i]
      for j in 0...nu do
        let t := α * x.uget xo xc rfl rfl hs.2.1 j (by lia)
        for i in 0...mu do
          have hk : (o + c * i).toNat < a.size := y.toNat_index_lt hs.2.2 (by lia)
          a[o + c * i] := a[o + c * i] + t * A.uget ao al rfl rfl hs.1 i j (by lia) (by lia)).2
  else y.data.modifyAt y.stride.idx 0 m (gemvSumAt α A x β)

public theorem gemvData_eq (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
    gemvData α A x β y = y.data.modifyAt y.stride.idx 0 m (gemvSumAt α A x β) := by
  unfold gemvData
  split
  · rename_i hs
    have he := y.loop_idx hs.2.2
    have hmu := y.toNat_toUSize hs.2.2
    have hnu := x.toNat_toUSize hs.2.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v) (he := he)
      (hg := fun _ _ _ _ => rfl)]
    rw [Tail.run_forInFrom_unit (F := fun j c => c.modifyAt y.stride.idx 0 m fun i v =>
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!) (hF := by simp)]
    · have hinj := y.fits.injOn (lo := 0) (Nat.le_refl _)
      simp only [Tail.run_done, USize.toNat_zero, hmu, hnu]
      rw [iterRange_modifyAt _ _ hinj, modifyAt_modifyAt _ _ hinj]
      rfl
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_modify (G := fun i v =>
          v + α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + i]!)
        (he := he)]
      · simp only [USize.toNat_zero, hmu]
      · intro i _ hi v
        rw [hmu] at hi
        rw [Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def,
          getElem!_pos x.data _ (x.index_lt hj), getElem!_pos A.data _ (A.index_lt hi hj)]
  · rfl

/--
`gemv α A x β y` is `α * A * x + β * y`, by the loops of the reference BLAS: it scales `y` by `β`,
then adds `α * x[j]` times column `j` of `A`, for `j = 0, …, n - 1`. As in the reference BLAS, it
returns `y` when `n = 0`, sets `y` to `0` without reading it when `β = 0`, and only scales `y` when
`α = 0`, without reading `A` or `x`. It updates `y` in place when its array is not shared, and
leaves the elements of the array outside `y` unchanged.
-/
@[expose] public def gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) : Vec m :=
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
public theorem data_gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
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

@[simp] public theorem off_gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
    (gemv α A x β y).off = y.off := by
  unfold gemv; split <;> (try split) <;> rfl

@[simp] public theorem inc_gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
    (gemv α A x β y).inc = y.inc := by
  unfold gemv; split <;> (try split) <;> rfl

/--
Element `i` of `gemv α A x β y` is `y[i]` when `n = 0`, `betaMul β y[i]` when `α = 0`, and
otherwise `betaMul β y[i]`, plus the terms `α * x[j] * A[i, j]` for `j = 0, …, n - 1`, added from
the left.
-/
@[simp] public theorem getElem_gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m)
    (i : Nat) (h : i < m) :
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
@[expose] public def gemvTSumAt (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (j : Nat)
    (v : Float) : Float :=
  betaMul β v + α * Nat.fold m
    (fun i _ s => s + A.data[A.off + A.ld * j + i]! * x.data[x.off + x.inc * i]!) 0

/--
The value of `gemvT` at the index `j` of `y`, from its old value `v`, on the arrays, with the
special cases of the reference BLAS: `v` when `m = 0`, and `betaMul β v` when `α = 0`.
-/
@[expose] public def gemvTAt (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (j : Nat)
    (v : Float) : Float :=
  if m = 0 then v else if α == 0 then betaMul β v else gemvTSumAt α A x β j v

/-- The array of `gemvT`. -/
public def gemvTData (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2.2
    let a := y.data
    let o := y.off.toUSize
    let c := y.inc.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    (inplace a do
      for j in 0...nu do
        have hk : (o + c * j).toNat < a.size := y.toNat_index_lt hs.2.2 (by lia)
        have hj : j.toNat < n := by lia
        a[o + c * j] := betaMul β a[o + c * j] + α * foldUpTo m
          (fun i hi s => s + A[(i, j.toNat)] * x[i])
          (fun i hi s => s + A.uget ao al rfl rfl hs.1 i j hi hj * x.uget xo xc rfl rfl hs.2.1 i hi)
          0).2
  else y.data.modifyAt y.stride.idx 0 n (gemvTSumAt α A x β)

public theorem gemvTData_eq (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    gemvTData α A x β y = y.data.modifyAt y.stride.idx 0 n (gemvTSumAt α A x β) := by
  unfold gemvTData
  split
  · rename_i hs
    have he := y.loop_idx hs.2.2
    have hnu := y.toNat_toUSize hs.2.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := gemvTSumAt α A x β) (he := he)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj v
      rw [hnu] at hj
      rw [foldUpTo_eq _ _ _ (by simp), gemvTSumAt]
      congr
      funext i hi s
      rw [getElem!_pos x.data _ (x.index_lt hi), getElem!_pos A.data _ (A.index_lt hi hj)]
      rfl
  · rfl

/--
`gemvT α A x β y` is `α * Aᵀ * x + β * y`, by the loops of the reference BLAS: for each `j`, it
sums the products `A[i, j] * x[i]` of column `j` of `A` and `x`, and adds `α` times the sum to
`β * y[j]`. As in the reference BLAS, it returns `y` when `m = 0`, sets `y[j]` to `0` without
reading it before adding the sum when `β = 0`, and only scales `y` when `α = 0`, without reading
`A` or `x`. It updates `y` in place when its array is not shared, and leaves the elements of the
array outside `y` unchanged.
-/
@[expose] public def gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
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
public theorem data_gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
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

@[simp] public theorem off_gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    (gemvT α A x β y).off = y.off := by
  unfold gemvT; split <;> (try split) <;> rfl

@[simp] public theorem inc_gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    (gemvT α A x β y).inc = y.inc := by
  unfold gemvT; split <;> (try split) <;> rfl

/--
Element `j` of `gemvT α A x β y` is `y[j]` when `m = 0`, `betaMul β y[j]` when `α = 0`, and
otherwise `betaMul β y[j] + α * s`, where `s` sums the terms `A[i, j] * x[i]` for
`i = 0, …, m - 1` from the left, starting at `0`.
-/
@[simp] public theorem getElem_gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float)
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
@[expose] public def gerAt (α : Float) (x : Vec m) (y : Vec n) (i j : Nat)
    (v : Float) : Float :=
  if y.data[y.off + y.inc * j]! == 0 then v
  else v + x.data[x.off + x.inc * i]! * (α * y.data[y.off + y.inc * j]!)

/--
The number of rows that the loop of `ger` updates in a column: `0` when `y[j] = 0`. It is not
inlined, so that the column loop has a single call site, which the C compiler inlines and
vectorizes.
-/
@[noinline, expose] public def gerRows (mu : USize) (yj : Float) : USize := if yj == 0 then 0 else mu

public theorem gerRows_le {mu : USize} (hmu : mu.toNat = m) (yj : Float) :
    (gerRows mu yj).toNat ≤ m := by
  unfold gerRows; split <;> simp [hmu]

/-- The array of `ger`. -/
public def gerData (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) : Float64Array :=
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

public theorem gerData_eq (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) :
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
@[expose] public def ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) : Mat m n :=
  if α == 0 then A
  else
    { data := gerData α x y A
      off := A.off
      ld := A.ld
      le_ld := A.le_ld
      bound := by rw [gerData_eq, size_mapMat]; exact A.bound }

/-- The array of `ger α x y A` is the array of `A` with its elements updated. -/
public theorem data_ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).data =
      mapMat A.data A.off A.ld m 0 n fun i j v => if α == 0 then v else gerAt α x y i j v := by
  unfold ger
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, gerData_eq]
  · simp only [↓reduceIte, mapMat_id]

@[simp] public theorem off_ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).off = A.off := by
  unfold ger; split <;> rfl

@[simp] public theorem ld_ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).ld = A.ld := by
  unfold ger; split <;> rfl

/--
Element `(i, j)` of `ger α x y A` is `A[i, j]` when `α = 0` or `y[j] = 0`, and
`A[i, j] + x[i] * (α * y[j])` otherwise.
-/
@[simp] public theorem getElem_ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (ger α x y A)[(i, j)] =
      if α == 0 || y[j] == 0 then A[(i, j)] else A[(i, j)] + x[i] * (α * y[j]) := by
  rw [getElem_of_data_eq_mapMat _ (data_ger α x y A) (off_ger α x y A) (ld_ger α x y A) i j h,
    gerAt,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt h.1),
    getElem!_pos y.data (y.off + y.inc * j) (y.index_lt h.2)]
  cases α == 0 <;> rfl

end Mat

end BLAS.Float64
