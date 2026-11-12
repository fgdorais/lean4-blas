/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Mat
public import BLAS.Float64.GemmBlocked

/-!
# `gemm` on matrices

`Mat.gemm` and `Mat.gemmBlocked` run the kernels of `PMat.gemm` and `PMat.gemmBlocked` on packed
matrices. A matrix that is packed already, from the index `0` with `ld = m` in an array of `m * n`,
goes to the kernel with no copy, and `C` is updated in place. Otherwise the matrix is packed into a
copy first, and the columns of the result are copied back into the array of `C`, which leaves the
other elements of that array unchanged. The copies take `m * k + k * n + 2 * m * n` steps against
the `2 * m * n * k` floating-point operations of the product.
-/

open ScalarArray Float64Array

namespace BLAS.Float64

namespace Mat

variable {m n k : Nat}

/-- Two matrices with the same array, offset and leading dimension are equal. -/
public theorem ext_data {A B : Mat m n} (hd : A.data = B.data) (ho : A.off = B.off)
    (hl : A.ld = B.ld) : A = B := by
  cases A; cases B; simp_all

/--
The value of `gemm α A B β C` at `(i, j)`: `β * C[i, j]`, plus the terms `α * B[l, j] * A[i, l]`
for `l = 0, …, k - 1`, added from the left, in the order of the reference BLAS.
-/
@[expose] public def gemmEntry (α : Float) (A : Mat m k) (B : Mat k n) (β : Float) (C : Mat m n)
    (i j : Nat) (hi : i < m) (hj : j < n) : Float :=
  Nat.fold k (fun l hl s => s + α * B[(l, j)] * A[(i, l)]) (β * C[(i, j)])

/-- `gemmEntry` at every element of a matrix, and the old value elsewhere. -/
@[expose] public def gemmAt (α : Float) (A : Mat m k) (B : Mat k n) (β : Float) (C : Mat m n)
    (i j : Nat) (v : Float) : Float :=
  if h : i < m ∧ j < n then gemmEntry α A B β C i j h.1 h.2 else v

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
    gemmBy f A B C = mapMat C.data C.off C.ld m 0 n (gemmAt α A B β C) := by
  have key : ∀ R : PMat m n, (∀ i j (h : i < m ∧ j < n), R[(i, j)] = C[(i, j)]) →
      unpack C (f A.pack B.pack R) = mapMat C.data C.off C.ld m 0 n (gemmAt α A B β C) := by
    intro R hR
    rw [unpack_eq]
    apply mapMat_congr
    intro i j v hi _ hj
    have hq := PMat.index_lt (m := m) hi hj
    rw [getElem!_pos _ _ (by rw [PMat.size_data]; exact hq), ← PMat.getElem_def _ _ _ ⟨hi, hj⟩,
      hf _ _ _ _ _ ⟨hi, hj⟩]
    simp only [gemmAt, hi, hj, and_self, dite_true, gemmEntry, PMat.gemmEntry, getElem_pack, hR]
  unfold gemmBy
  split
  · rename_i h
    rw [← unpack_of_isPacked C h, key]
    intro i j hij
    simp only [PMat.getElem_def, getElem_def, h.1, h.2.1]
    congr 1
    omega
  · exact key _ (fun i j h => getElem_pack C i j h)

/--
`gemm α A B β C` is `α * A * B + β * C`, by the naive loops of the reference BLAS, over `C`. It
updates `C` in place when `C` is packed and its array is not shared. It leaves the elements of
`C`'s array outside `C` unchanged. Unlike the reference BLAS, it doesn't special-case `β = 0`, so a
`NaN` in `C` stays a `NaN`.
-/
@[expose] public def gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float) (C : Mat m n) :
    Mat m n where
  data := gemmBy (PMat.gemm α · · β ·) A B C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by
    rw [gemmBy_eq α β _ (fun P Q R i j h => PMat.getElem_gemm α P Q β R i j h), size_mapMat]
    exact C.bound

/-- The array of `gemm α A B β C` is the array of `C` with its elements updated. -/
public theorem data_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float) (C : Mat m n) :
    (gemm α A B β C).data = mapMat C.data C.off C.ld m 0 n (gemmAt α A B β C) :=
  gemmBy_eq α β _ (fun P Q R i j h => PMat.getElem_gemm α P Q β R i j h) A B C

@[simp] public theorem off_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : (gemm α A B β C).off = C.off := rfl

@[simp] public theorem ld_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : (gemm α A B β C).ld = C.ld := rfl

@[simp] public theorem getElem_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemm α A B β C)[(i, j)] = gemmEntry α A B β C i j h.1 h.2 := by
  rw [getElem_of_data_eq_mapMat _ (data_gemm α A B β C) rfl rfl i j h]
  simp [gemmAt, h.1, h.2]

/--
`gemmBlocked α A B β C` is `gemm α A B β C`, about twice as fast, by the blocked loops of
`PMat.gemmBlocked`.
-/
@[expose] public def gemmBlocked (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : Mat m n where
  data := gemmBy (PMat.gemmBlocked α · · β ·) A B C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by
    rw [gemmBy_eq α β _ (fun P Q R i j h => PMat.getElem_gemmBlocked α P Q β R i j h), size_mapMat]
    exact C.bound

/-- The array of `gemmBlocked α A B β C` is the array of `C` with its elements updated. -/
public theorem data_gemmBlocked (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) :
    (gemmBlocked α A B β C).data = mapMat C.data C.off C.ld m 0 n (gemmAt α A B β C) :=
  gemmBy_eq α β _ (fun P Q R i j h => PMat.getElem_gemmBlocked α P Q β R i j h) A B C

/-- `gemmBlocked` computes the same matrix as `gemm`, to the bit. -/
public theorem gemmBlocked_eq_gemm (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) : gemmBlocked α A B β C = gemm α A B β C := by
  refine ext_data ?_ rfl rfl
  rw [data_gemmBlocked, data_gemm]

@[simp] public theorem getElem_gemmBlocked (α : Float) (A : Mat m k) (B : Mat k n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmBlocked α A B β C)[(i, j)] = gemmEntry α A B β C i j h.1 h.2 := by
  rw [gemmBlocked_eq_gemm, getElem_gemm]

end Mat

end BLAS.Float64
