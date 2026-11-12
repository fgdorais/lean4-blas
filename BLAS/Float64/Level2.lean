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

/-- The value of `gemv` at the index `i` of `y`, from its old value `v`, on the arrays. -/
@[expose] public def gemvAt (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (i : Nat)
    (v : Float) : Float :=
  Nat.fold n (fun j _ s => s + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!)
    (β * v)

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
        have hk : (o + c * i).toNat < a.size := y.toNat_index_lt hs.2.2 (by omega)
        a[o + c * i] := β * a[o + c * i]
      for j in 0...nu do
        let t := α * x.uget xo xc rfl rfl hs.2.1 j (by omega)
        for i in 0...mu do
          have hk : (o + c * i).toNat < a.size := y.toNat_index_lt hs.2.2 (by omega)
          a[o + c * i] := a[o + c * i] + t * A.uget ao al rfl rfl hs.1 i j (by omega) (by omega)).2
  else mapStride y.data y.off y.inc 0 m (gemvAt α A x β)

public theorem gemvData_eq (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
    gemvData α A x β y = mapStride y.data y.off y.inc 0 m (gemvAt α A x β) := by
  unfold gemvData
  split
  · rename_i hs
    obtain ⟨hinc, hix⟩ := y.loop_facts hs.2.2
    have hmu := y.toNat_toUSize hs.2.2
    have hnu := x.toNat_toUSize hs.2.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [run_forInFrom_stride (G := fun _ v => β * v) (OFF := _) (INC := _) (hinc := hinc)
      (hix := hix) (hg := fun _ _ _ => rfl)]
    rw [run_forInFrom_iter (F := fun j c => mapStride c y.off y.inc 0 m fun i v =>
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!) (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hmu, hnu]
      rw [iterRange_mapStride, mapStride_mapStride]
      rfl
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [run_forInFrom_stride (G := fun i v =>
          v + α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + i]!)
        (OFF := _) (INC := _) (hinc := hinc) (hix := hix)]
      · simp only [USize.toNat_zero, hmu]
      · intro i hi v
        rw [hmu] at hi
        rw [Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def,
          getElem!_pos x.data _ (x.index_lt hj), getElem!_pos A.data _ (A.index_lt hi hj)]
  · rfl

/--
`gemv α A x β y` is `α * A * x + β * y`, by the loops of the reference BLAS: it scales `y` by `β`,
then adds `α * x[j]` times column `j` of `A`, for `j = 0, …, n - 1`. It updates `y` in place when
its array is not shared, and leaves the elements of the array outside `y` unchanged. Unlike the
reference BLAS, it doesn't special-case `β = 0`, so a `NaN` in `y` stays a `NaN`.
-/
@[expose] public def gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) : Vec m where
  data := gemvData α A x β y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [gemvData_eq, size_mapStride]; exact y.bound

/-- The array of `gemv α A x β y` is the array of `y` with its elements updated. -/
public theorem data_gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
    (gemv α A x β y).data = mapStride y.data y.off y.inc 0 m (gemvAt α A x β) :=
  gemvData_eq α A x β y

@[simp] public theorem off_gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
    (gemv α A x β y).off = y.off := rfl

@[simp] public theorem inc_gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) :
    (gemv α A x β y).inc = y.inc := rfl

/--
Element `i` of `gemv α A x β y` is `β * y[i]`, plus the terms `α * x[j] * A[i, j]` for
`j = 0, …, n - 1`, added from the left.
-/
@[simp] public theorem getElem_gemv (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m)
    (i : Nat) (h : i < m) :
    (gemv α A x β y)[i] = Nat.fold n (fun j _ s => s + α * x[j] * A[(i, j)]) (β * y[i]) := by
  rw [Vec.getElem_of_data_eq_mapStride _ (data_gemv α A x β y) rfl rfl i h, gemvAt]
  congr
  funext j hj s
  rw [getElem!_pos x.data _ (x.index_lt hj), getElem!_pos A.data _ (A.index_lt h hj)]
  rfl

/-! ## `gemvT` -/

/-- The value of `gemvT` at the index `j` of `y`, from its old value `v`, on the arrays. -/
@[expose] public def gemvTAt (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (j : Nat)
    (v : Float) : Float :=
  β * v + α * Nat.fold m
    (fun i _ s => s + A.data[A.off + A.ld * j + i]! * x.data[x.off + x.inc * i]!) 0

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
        have hk : (o + c * j).toNat < a.size := y.toNat_index_lt hs.2.2 (by omega)
        have hj : j.toNat < n := by omega
        a[o + c * j] := β * a[o + c * j] + α * foldUpTo m
          (fun i hi s => s + A[(i, j.toNat)] * x[i])
          (fun i hi s => s + A.uget ao al rfl rfl hs.1 i j hi hj * x.uget xo xc rfl rfl hs.2.1 i hi)
          0).2
  else mapStride y.data y.off y.inc 0 n (gemvTAt α A x β)

public theorem gemvTData_eq (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    gemvTData α A x β y = mapStride y.data y.off y.inc 0 n (gemvTAt α A x β) := by
  unfold gemvTData
  split
  · rename_i hs
    obtain ⟨hinc, hix⟩ := y.loop_facts hs.2.2
    have hnu := y.toNat_toUSize hs.2.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [run_forInFrom_stride (G := gemvTAt α A x β) (OFF := _) (INC := _) (hinc := hinc)
      (hix := hix)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j hj v
      rw [hnu] at hj
      rw [foldUpTo_eq _ _ _ (by simp), gemvTAt]
      congr
      funext i hi s
      rw [getElem!_pos x.data _ (x.index_lt hi), getElem!_pos A.data _ (A.index_lt hi hj)]
      rfl
  · rfl

/--
`gemvT α A x β y` is `α * Aᵀ * x + β * y`, by the loops of the reference BLAS: for each `j`, it
sums the products `A[i, j] * x[i]` of column `j` of `A` and `x`, and adds `α` times the sum to
`β * y[j]`. It updates `y` in place when its array is not shared, and leaves the elements of the
array outside `y` unchanged.
-/
@[expose] public def gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    Vec n where
  data := gemvTData α A x β y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [gemvTData_eq, size_mapStride]; exact y.bound

/-- The array of `gemvT α A x β y` is the array of `y` with its elements updated. -/
public theorem data_gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    (gemvT α A x β y).data = mapStride y.data y.off y.inc 0 n (gemvTAt α A x β) :=
  gemvTData_eq α A x β y

@[simp] public theorem off_gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    (gemvT α A x β y).off = y.off := rfl

@[simp] public theorem inc_gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) :
    (gemvT α A x β y).inc = y.inc := rfl

/--
Element `j` of `gemvT α A x β y` is `β * y[j] + α * s`, where `s` sums the terms
`A[i, j] * x[i]` for `i = 0, …, m - 1` from the left, starting at `0`.
-/
@[simp] public theorem getElem_gemvT (α : Float) (A : Mat m n) (x : Vec m) (β : Float)
    (y : Vec n) (j : Nat) (h : j < n) :
    (gemvT α A x β y)[j] =
      β * y[j] + α * Nat.fold m (fun i _ s => s + A[(i, j)] * x[i]) 0 := by
  rw [Vec.getElem_of_data_eq_mapStride _ (data_gemvT α A x β y) rfl rfl j h, gemvTAt]
  congr
  funext i hi s
  rw [getElem!_pos x.data _ (x.index_lt hi), getElem!_pos A.data _ (A.index_lt hi h)]
  rfl

/-! ## `ger` -/

/-- The value of `ger` at `(i, j)`, from its old value `v`, on the arrays. -/
@[expose] public def gerAt (α : Float) (x : Vec m) (y : Vec n) (i j : Nat)
    (v : Float) : Float :=
  v + x.data[x.off + x.inc * i]! * (α * y.data[y.off + y.inc * j]!)

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
        let t := α * y.uget yo yc rfl rfl hs.2.2 j (by omega)
        let cj := ao + al * j
        for i in 0...mu do
          have hk : (cj + 1 * i).toNat < a.size := A.toNat_col_index_lt hs.1 (by omega) (by omega)
          a[cj + 1 * i] := a[cj + 1 * i] + x.uget xo xc rfl rfl hs.2.1 i (by omega) * t).2
  else mapMat A.data A.off A.ld m 0 n (gerAt α x y)

public theorem gerData_eq (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) :
    gerData α x y A = mapMat A.data A.off A.ld m 0 n (gerAt α x y) := by
  unfold gerData
  split
  · rename_i hs
    have hmu := x.toNat_toUSize hs.2.1
    have hnu := y.toNat_toUSize hs.2.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [run_forInFrom_iter (F := fun j c => mapStride c (A.off + A.ld * j) 1 0 m fun i v =>
      gerAt α x y i j v) (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ A.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [run_forInFrom_stride (G := fun i v => gerAt α x y i j.toNat v)
        (OFF := A.off + A.ld * j.toNat) (INC := 1) (hinc := Or.inl Nat.one_pos)
        (hix := fun i hi => A.toNat_col_index hs.1 (by omega) hj)]
      · simp only [USize.toNat_zero, hmu]
      · intro i hi v
        rw [hmu] at hi
        rw [Vec.uget_eq_getElem, Vec.uget_eq_getElem, Vec.getElem_def, Vec.getElem_def, gerAt,
          getElem!_pos x.data (x.off + x.inc * i.toNat) (x.index_lt hi),
          getElem!_pos y.data (y.off + y.inc * j.toNat) (y.index_lt hj)]
  · rfl

/--
`ger α x y A` is `α * x * yᵀ + A`, by the loops of the reference BLAS: for each column `j`, it
adds `x` times `α * y[j]`. It updates `A` in place when its array is not shared, and leaves the
elements of the array outside `A` unchanged. Unlike the reference BLAS, it doesn't skip the
columns with `y[j] = 0`, so an infinity or a `NaN` in `x` reaches every column.
-/
@[expose] public def ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) : Mat m n where
  data := gerData α x y A
  off := A.off
  ld := A.ld
  le_ld := A.le_ld
  bound := by rw [gerData_eq, size_mapMat]; exact A.bound

/-- The array of `ger α x y A` is the array of `A` with its elements updated. -/
public theorem data_ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).data = mapMat A.data A.off A.ld m 0 n (gerAt α x y) :=
  gerData_eq α x y A

@[simp] public theorem off_ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).off = A.off := rfl

@[simp] public theorem ld_ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) :
    (ger α x y A).ld = A.ld := rfl

/-- Element `(i, j)` of `ger α x y A` is `A[i, j] + x[i] * (α * y[j])`. -/
@[simp] public theorem getElem_ger (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) : (ger α x y A)[(i, j)] = A[(i, j)] + x[i] * (α * y[j]) := by
  rw [getElem_of_data_eq_mapMat _ (data_ger α x y A) rfl rfl i j h, gerAt,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt h.1),
    getElem!_pos y.data (y.off + y.inc * j) (y.index_lt h.2)]
  rfl

end Mat

end BLAS.Float64
