/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Mat
public import BLAS.Float64.GemmBlocked

/-!
# `gemm` on matrices

`Mat.gemm` runs the kernel of `PMat.gemmBlocked`, and `Mat.gemmNaive` the kernel of `PMat.gemm`,
which has the naive loops of the reference BLAS, on packed matrices. A matrix that is packed
already, from the index `0` with `ld = m` in an array of `m * n`, goes to the kernel with no copy,
and `C` is updated in place. Otherwise the matrix is packed into a copy first, and the columns of
the result are copied back into the array of `C`, which leaves the other elements of that array
unchanged. The copies take `m * k + k * n + 2 * m * n` steps against the `2 * m * n * k`
floating-point operations of the product.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {m n k : Nat}

/-- Two matrices with the same array, offset and leading dimension are equal. -/
public theorem ext_data {A B : Mat m n} (hd : A.data = B.data) (ho : A.off = B.off)
    (hl : A.ld = B.ld) : A = B := by
  cases A; cases B; simp_all

/--
The value of the loops of `gemm α A B β C` at `(i, j)`: `betaMul β C[i, j]`, plus the terms
`α * B[l, j] * A[i, l]` for `l = 0, …, k - 1`, added from the left, in the order of the reference
BLAS.
-/
@[expose] public def gemmSumEntry (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) (i j : Nat) (hi : i < m) (hj : j < n) : Float :=
  Nat.fold k (fun l hl s => s + α * B[(l, j)] * A[(i, l)]) (betaMul β C[(i, j)])

/--
The value of `gemm α A B β C` at `(i, j)`: `betaMul β C[i, j]` when `α = 0`, as the reference
BLAS only scales `C` then, and `gemmSumEntry` otherwise.
-/
@[expose] public def gemmEntry (α : Float) (A : Mat m k) (B : Mat k n) (β : Float) (C : Mat m n)
    (i j : Nat) (hi : i < m) (hj : j < n) : Float :=
  if α == 0 then betaMul β C[(i, j)] else gemmSumEntry α A B β C i j hi hj

/-- `gemmSumEntry` at every element of a matrix, and the old value elsewhere. -/
@[expose] public def gemmSumAt (α : Float) (A : Mat m k) (B : Mat k n) (β : Float) (C : Mat m n)
    (i j : Nat) (v : Float) : Float :=
  if h : i < m ∧ j < n then gemmSumEntry α A B β C i j h.1 h.2 else v

/-- `gemmEntry` at every element of a matrix, and the old value elsewhere. -/
@[expose] public def gemmAt (α : Float) (A : Mat m k) (B : Mat k n) (β : Float) (C : Mat m n)
    (i j : Nat) (v : Float) : Float :=
  if h : i < m ∧ j < n then gemmEntry α A B β C i j h.1 h.2 else v

/--
The array of `C` scaled by `betaMul β`, as the reference BLAS scales `C` in `gemm` when `α = 0`:
by `β`, or set to `0` without reading it when `β = 0`.
-/
public def scalBetaData (β : Float) (C : Mat m n) : Float64Array :=
  if hs : C.data.size < USize.size ∧ m < USize.size ∧ n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let a := C.data
    let co := C.off.toUSize
    let cl := C.ld.toUSize
    (inplace a do
      for j in 0...nu do
        let cj := co + cl * j
        for i in 0...mu do
          have hk : (cj + 1 * i).toNat < a.size := C.toNat_col_index_lt hs.1 (by lia) (by lia)
          a[cj + 1 * i] := betaMul β a[cj + 1 * i]).2
  else mapMat C.data C.off C.ld m 0 n fun _ _ v => betaMul β v

public theorem scalBetaData_eq (β : Float) (C : Mat m n) :
    scalBetaData β C = mapMat C.data C.off C.ld m 0 n fun _ _ v => betaMul β v := by
  unfold scalBetaData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 m fun _ v => betaMul β v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ C.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v)
        (idx := (Stride.mk (C.off + C.ld * j.toNat) 1).idx)
        (he := fun i _ hi => C.toNat_col_index hs.1 (by lia) hj)]
      · simp only [USize.toNat_zero, hmu]
      · intro _ _ _ _; rfl
  · rfl

/--
The array of a `gemm` by the kernel `f` on packed matrices: `C`'s array when `C` is packed, and a
copy of the columns of the result into `C`'s array otherwise.
-/
public def gemmBy (f : PMat m k → PMat k n → PMat m n → PMat m n) (A : Mat m k) (B : Mat k n)
    (C : Mat m n) : Float64Array :=
  if h : C.IsPacked then (f A.pack B.pack ⟨C.data, h.2.2⟩).data
  else unpack C (f A.pack B.pack C.pack)

/-- The array of a `gemm` by a kernel that computes `PMat.gemmEntry`. -/
public theorem gemmBy_eq (α β : Float) (f : PMat m k → PMat k n → PMat m n → PMat m n)
    (hf : ∀ P Q R i j (h : i < m ∧ j < n),
      (f P Q R)[(i, j)] = PMat.gemmEntry α P Q β R i j h.1 h.2)
    (A : Mat m k) (B : Mat k n) (C : Mat m n) :
    gemmBy f A B C = mapMat C.data C.off C.ld m 0 n (gemmSumAt α A B β C) := by
  have key : ∀ R : PMat m n, (∀ i j (h : i < m ∧ j < n), R[(i, j)] = C[(i, j)]) →
      unpack C (f A.pack B.pack R) = mapMat C.data C.off C.ld m 0 n (gemmSumAt α A B β C) := by
    intro R hR
    rw [unpack_eq]
    apply mapMat_congr
    intro i j v hi _ hj
    have hq := PMat.index_lt (m := m) hi hj
    rw [getElem!_pos _ _ (by rw [PMat.size_data]; exact hq), ← PMat.getElem_def _ _ _ ⟨hi, hj⟩,
      hf _ _ _ _ _ ⟨hi, hj⟩]
    simp only [gemmSumAt, hi, hj, and_self, dite_true, gemmSumEntry, PMat.gemmEntry, getElem_pack,
      hR]
  unfold gemmBy
  split
  · rename_i h
    rw [← unpack_of_isPacked C h, key]
    intro i j hij
    simp only [PMat.getElem_def, getElem_def, h.1, h.2.1]
    congr 1
    lia
  · exact key _ (fun i j h => getElem_pack C i j h)

/--
`gemmNaive α A B β C` is `α * A * B + β * C`, by the naive loops of the reference BLAS, over `C`,
and `gemm` computes the same matrix faster. It
updates `C` in place when `C` is packed and its array is not shared. It leaves the elements of
`C`'s array outside `C` unchanged. As in the reference BLAS, it sets `C` to `0` without reading it
when `β = 0`, before adding the products, and only scales `C` when `α = 0`, without reading `A` or
`B`.
-/
@[expose] public def gemmNaive (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : Mat m n :=
  if α == 0 then
    { data := C.scalBetaData β
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [scalBetaData_eq, size_mapMat]; exact C.bound }
  else
    { data := gemmBy (PMat.gemm α · · β ·) A B C
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by
        rw [gemmBy_eq α β _ (fun P Q R i j h => PMat.getElem_gemm α P Q β R i j h), size_mapMat]
        exact C.bound }

/-- The array of a `gemm` by a kernel that computes `PMat.gemmEntry`, or of its case `α = 0`. -/
theorem gemmData_eq (α β : Float) (f : PMat m k → PMat k n → PMat m n → PMat m n)
    (hf : ∀ P Q R i j (h : i < m ∧ j < n),
      (f P Q R)[(i, j)] = PMat.gemmEntry α P Q β R i j h.1 h.2)
    (A : Mat m k) (B : Mat k n) (C : Mat m n) :
    (if α == 0 then C.scalBetaData β else gemmBy f A B C) =
      mapMat C.data C.off C.ld m 0 n (gemmAt α A B β C) := by
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, gemmBy_eq α β f hf]
    exact mapMat_congr _ _ _ _ _ _ fun i j v hi _ hj => by
      simp [gemmAt, gemmSumAt, gemmEntry, hi, hj, hα]
  · simp only [↓reduceIte, scalBetaData_eq]
    exact mapMat_congr_getElem _ _ _ _ _ _ fun i j hi _ hj _ => by
      simp [gemmAt, gemmEntry, hi, hj, hα, getElem_def]

/-- The array of `gemmNaive α A B β C` is the array of `C` with its elements updated. -/
public theorem data_gemmNaive (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) :
    (gemmNaive α A B β C).data = mapMat C.data C.off C.ld m 0 n (gemmAt α A B β C) := by
  rw [← gemmData_eq α β _ (fun P Q R i j h => PMat.getElem_gemm α P Q β R i j h) A B C]
  unfold gemmNaive; split <;> simp_all

@[simp] public theorem off_gemmNaive (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : (gemmNaive α A B β C).off = C.off := by
  unfold gemmNaive; split <;> rfl

@[simp] public theorem ld_gemmNaive (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : (gemmNaive α A B β C).ld = C.ld := by
  unfold gemmNaive; split <;> rfl

@[simp] public theorem getElem_gemmNaive (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmNaive α A B β C)[(i, j)] = gemmEntry α A B β C i j h.1 h.2 := by
  rw [getElem_of_data_eq_mapMat _ (data_gemmNaive α A B β C) (off_gemmNaive α A B β C)
    (ld_gemmNaive α A B β C) i j h]
  simp [gemmAt, h.1, h.2]

/--
`gemm α A B β C` is `α * A * B + β * C`, over `C`, by the blocked loops of `PMat.gemmBlocked`. Each
element gets the operations of the naive loops of the reference BLAS, in the same order, so the
result is that of `gemmNaive` to the bit, about twice as fast. It updates `C` in place when `C` is
packed and its array is not shared. It leaves the elements of `C`'s array outside `C` unchanged. As
in the reference BLAS, it sets `C` to `0` without reading it when `β = 0`, before adding the
products, and only scales `C` when `α = 0`, without reading `A` or `B`.
-/
@[expose] public def gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : Mat m n :=
  if α == 0 then
    { data := C.scalBetaData β
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [scalBetaData_eq, size_mapMat]; exact C.bound }
  else
    { data := gemmBy (PMat.gemmBlocked α · · β ·) A B C
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by
        rw [gemmBy_eq α β _ (fun P Q R i j h => PMat.getElem_gemmBlocked α P Q β R i j h),
          size_mapMat]
        exact C.bound }

/-- The array of `gemm α A B β C` is the array of `C` with its elements updated. -/
public theorem data_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) :
    (gemm α A B β C).data = mapMat C.data C.off C.ld m 0 n (gemmAt α A B β C) := by
  rw [← gemmData_eq α β _ (fun P Q R i j h => PMat.getElem_gemmBlocked α P Q β R i j h) A B C]
  unfold gemm; split <;> simp_all

@[simp] public theorem off_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : (gemm α A B β C).off = C.off := by
  unfold gemm; split <;> rfl

@[simp] public theorem ld_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : (gemm α A B β C).ld = C.ld := by
  unfold gemm; split <;> rfl

/-- `gemm` computes the same matrix as `gemmNaive`, to the bit. -/
public theorem gemm_eq_gemmNaive (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : gemm α A B β C = gemmNaive α A B β C :=
  ext_data (by rw [data_gemm, data_gemmNaive]) (by simp) (by simp)

@[simp] public theorem getElem_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemm α A B β C)[(i, j)] = gemmEntry α A B β C i j h.1 h.2 := by
  rw [gemm_eq_gemmNaive, getElem_gemmNaive]

end Mat

end BLAS.Float64
