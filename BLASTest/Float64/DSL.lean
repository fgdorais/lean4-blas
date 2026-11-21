/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
import BLAS.Notation
import BLASTest.Util
meta import BLAS
meta import BLAS.Notation
meta import BLASTest.Util

/-!
Tests for the `blas%` notation on `Float`: the routine of each update, its values, and the updates
that no single routine computes.
-/

open BLAS BLAS.Float64 BLAS.Notation

/-! ## Expansions

Each update is one call of its routine, which `simp` unfolds, so the routine's specification
applies. -/

section

variable {m k n : Nat} (α β : Float)

example (A : Mat m n) (x : Vec n) (y : Vec m) :
    blas%(y := α • A * x + β • y) = Mat.gemv α A x β y := by simp

example (A : Mat m n) (x : Vec n) (y : Vec m) :
    blas%(y := β • y + α • A * x) = Mat.gemv α A x β y := by simp

-- A scalar is a product or quotient of terms, with no parentheses.
example (a : Float) (A : Mat m n) (x : Vec n) (y : Vec m) :
    blas%(y := 2 * a • A * x + -β / 2 • y) = Mat.gemv (2 * a) A x (-β / 2) y := by simp

example (a : Float) (x y : Vec n) : blas%(y := (a + β) • x + y) = Vec.axpy (a + β) x y := by
  simp

example (A : Mat m n) (x : Vec n) (y : Vec m) : blas%(y := A * x) = Mat.gemv 1 A x 0 y := by
  simp

example (A : Mat m n) (x : Vec n) (y : Vec m) : blas%(y += α • A * x) = Mat.gemv α A x 1 y := by
  simp

example (A : Mat m n) (x : Vec m) (y : Vec n) :
    blas%(y := α • Aᵀ * x + β • y) = Mat.gemvT α A x β y := by simp

example (A : Mat m k) (B : Mat k n) (C : Mat m n) :
    blas%(C := α • A * B + β • C) = Mat.gemm α A B β C := by simp

example (A : Mat m k) (B : Mat k n) (C : Mat m n) : blas%(C += A * B) = Mat.gemm 1 A B 1 C := by
  simp

example (A : Mat k m) (B : Mat k n) (C : Mat m n) :
    blas%(C := α • Aᵀ * B + β • C) = Mat.gemmTN α A B β C := by simp

example (A : Mat m k) (B : Mat n k) (C : Mat m n) :
    blas%(C += A * Bᵀ) = Mat.gemmNT 1 A B 1 C := by simp

example (A : Mat k m) (B : Mat n k) (C : Mat m n) :
    blas%(C := Aᵀ * Bᵀ) = Mat.gemmTT 1 A B 0 C := by simp

example (x y : Vec n) : blas%(y := α • x + y) = Vec.axpy α x y := by simp

example (x y : Vec n) : blas%(y := α • x + β • y) = Vec.axpby α x β y := by simp

example (x y : Vec n) : blas%(y := α • x) = Vec.axpby α x 0 y := by simp

example (x y : Vec n) : blas%(y := x - y) = Vec.axpby 1 x (-1) y := by simp

example (x y : Vec n) : blas%(y += x) = Vec.axpy 1 x y := by simp

example (x : Vec n) : blas%(x := α • x) = Vec.scal α x := by simp

example (x y : Vec n) : blas%(y := x) = Vec.copy x y := by simp

example (A : Mat n n) (x : Vec n) : blas%(x := A.lower⁻¹ * x) = Mat.trsv .lower .nonUnit A x := by
  simp

example (A : Mat n n) (x : Vec n) : blas%(x := A.unitUpper⁻¹ * x) = Mat.trsv .upper .unit A x :=
  by simp

example (A : Mat m m) (B : Mat m n) :
    blas%(B := α • A.lower⁻¹ * B) = Mat.trsm .lower .nonUnit α A B := by simp

example (A : Mat n n) (B : Mat m n) :
    blas%(B := α • B * A.unitUpper⁻¹) = Mat.trsmRight .upper .unit α A B := by simp

example (A : Mat n n) (x : Vec n) :
    blas%(x := A.lowerᵀ⁻¹ * x) = Mat.trsvT .lower .nonUnit A x := by simp

example (A : Mat m m) (B : Mat m n) :
    blas%(B := α • A.unitUpperᵀ⁻¹ * B) = Mat.trsmT .upper .unit α A B := by simp

example (A : Mat m m) (B : Mat m n) :
    blas%(B := A.upperᵀ⁻¹ * B) = Mat.trsmT .upper .nonUnit 1 A B := by simp

example (A : Mat n n) (B : Mat m n) :
    blas%(B := B * A.lowerᵀ⁻¹) = Mat.trsmRightT .lower .nonUnit 1 A B := by simp

-- A product over one of its operands, by a triangle, is `trmv` or `trmm`.
example (A : Mat n n) (x : Vec n) : blas%(x := A.upper * x) = Mat.trmv .upper .nonUnit A x := by
  simp

example (A : Mat n n) (x : Vec n) : blas%(x := A.unitLowerᵀ * x) = Mat.trmvT .lower .unit A x :=
  by simp

example (A : Mat m m) (B : Mat m n) :
    blas%(B := α • A.lower * B) = Mat.trmm .lower .nonUnit α A B := by simp

example (A : Mat m m) (B : Mat m n) : blas%(B := A.upperᵀ * B) = Mat.trmmT .upper .nonUnit 1 A B :=
  by simp

example (A : Mat n n) (B : Mat m n) :
    blas%(B := α • B * A.unitUpper) = Mat.trmmRight .upper .unit α A B := by simp

example (A : Mat n n) (B : Mat m n) :
    blas%(B := B * A.lowerᵀ) = Mat.trmmRightT .lower .nonUnit 1 A B := by simp

-- A symmetric matrix is `symv`, `symm` or `symmRight`.
example (A : Mat n n) (x y : Vec n) :
    blas%(y := α • A.symLower * x + β • y) = Mat.symv .lower α A x β y := by simp

example (A : Mat m m) (B C : Mat m n) :
    blas%(C += A.symUpper * B) = Mat.symm .upper 1 A B 1 C := by simp

example (A : Mat n n) (B C : Mat m n) :
    blas%(C := α • B * A.symLower) = Mat.symmRight .lower α A B 0 C := by simp

-- A band view is `gbmv`, `gbmvT`, `sbmv`, `tbmv`, `tbmvT`, `tbsv` or `tbsvT`.
example (A : Mat 4 n) (x : Vec n) (y : Vec m) :
    blas%(y := α • A.band m 1 2 * x + β • y) = Mat.gbmv 1 2 α A x β y := by simp

example (A : Mat 4 n) (x : Vec m) (y : Vec n) :
    blas%(y += (A.band m 2 1)ᵀ * x) = Mat.gbmvT 2 1 1 A x 1 y := by simp

example (A : Mat (k + 1) n) (x y : Vec n) :
    blas%(y := α • A.symUpperBand * x + β • y) = Mat.sbmv .upper α A x β y := by simp

example (A : Mat (k + 1) n) (x : Vec n) :
    blas%(x := A.lowerBand * x) = Mat.tbmv .lower .nonUnit A x := by simp

example (A : Mat (k + 1) n) (x : Vec n) :
    blas%(x := A.unitUpperBandᵀ * x) = Mat.tbmvT .upper .unit A x := by simp

example (A : Mat (k + 1) n) (x : Vec n) :
    blas%(x := A.upperBand⁻¹ * x) = Mat.tbsv .upper .nonUnit A x := by simp

example (A : Mat (k + 1) n) (x : Vec n) :
    blas%(x := A.unitLowerBandᵀ⁻¹ * x) = Mat.tbsvT .lower .unit A x := by simp

-- A packed view is `spmv`, `tpmv`, `tpmvT`, `tpsv` or `tpsvT`, and a target `spr` or `spr2`.
example (ap : Vec (n * (n + 1) / 2)) (x y : Vec n) :
    blas%(y := α • ap.symLowerPacked * x + β • y) = Mat.spmv .lower α ap x β y := by simp

example (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    blas%(x := ap.upperPacked * x) = Mat.tpmv .upper .nonUnit ap x := by simp

example (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    blas%(x := ap.unitLowerPackedᵀ * x) = Mat.tpmvT .lower .unit ap x := by simp

example (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    blas%(x := ap.lowerPacked⁻¹ * x) = Mat.tpsv .lower .nonUnit ap x := by simp

example (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    blas%(x := ap.unitUpperPackedᵀ⁻¹ * x) = Mat.tpsvT .upper .unit ap x := by simp

example (x : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    blas%(ap.symUpperPacked += α • x * xᵀ) = Mat.spr .upper α x ap := by simp

example (x y : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    blas%(ap.symLowerPacked += α • x * yᵀ + α • y * xᵀ) = Mat.spr2 .lower α x y ap := by simp

-- A rank-one update is `ger`.
example (x : Vec m) (y : Vec n) (A : Mat m n) : blas%(A += α • x * yᵀ) = Mat.ger α x y A := by
  simp

example (x : Vec m) (y : Vec n) (A : Mat m n) : blas%(A -= x * yᵀ) = Mat.ger (-1) x y A := by
  simp

-- A triangle target `C.lower` updates only that triangle of `C`.
example (A : Mat n k) (B : Mat k n) (C : Mat n n) :
    blas%(C.lower := α • A * B + β • C.lower) = Mat.gemmtr .lower α A B β C := by simp

example (A B : Mat k n) (C : Mat n n) :
    blas%(C.upper += Aᵀ * B) = Mat.gemmtrTN .upper 1 A B 1 C := by simp

example (A B : Mat n k) (C : Mat n n) :
    blas%(C.upper := A * Bᵀ) = Mat.gemmtrNT .upper 1 A B 0 C := by simp

example (A : Mat k n) (B : Mat n k) (C : Mat n n) :
    blas%(C.lower := Aᵀ * Bᵀ - C.lower) = Mat.gemmtrTT .lower 1 A B (-1) C := by simp

example (A : Mat n k) (C : Mat n n) :
    blas%(C.lower := α • A * Aᵀ + β • C.lower) = Mat.syrk .lower α A β C := by simp

example (A : Mat k n) (C : Mat n n) :
    blas%(C.upper -= Aᵀ * A) = Mat.syrkT .upper (-1) A 1 C := by simp

example (x : Vec n) (A : Mat n n) : blas%(A.lower += α • x * xᵀ) = Mat.syr .lower α x A := by
  simp

example (A B : Mat n k) (C : Mat n n) :
    blas%(C.lower := α • A * Bᵀ + α • B * Aᵀ + β • C.lower) = Mat.syr2k .lower α A B β C := by
  simp

example (A B : Mat k n) (C : Mat n n) :
    blas%(C.upper := Aᵀ * B + Bᵀ * A) = Mat.syr2kT .upper 1 A B 0 C := by simp

example (x y : Vec n) (A : Mat n n) :
    blas%(A.upper += α • x * yᵀ + α • y * xᵀ) = Mat.syr2 .upper α x y A := by simp

-- A subtracted summand has the negated scalar.
example (A : Mat m n) (x : Vec n) (y : Vec m) : blas%(y := A * x - y) = Mat.gemv 1 A x (-1) y :=
  by simp

example (A : Mat m n) (x : Vec n) (y : Vec m) : blas%(y -= A * x) = Mat.gemv (-1) A x 1 y := by
  simp

example (A : Mat m k) (B : Mat k n) (C : Mat m n) :
    blas%(C := -α • A * B - β • C) = Mat.gemm (-α) A B (-β) C := by simp

example (x y : Vec n) : blas%(y := y - α • x) = Vec.axpy (-α) x y := by simp

example (x y : Vec n) : blas%(y -= α • x) = Vec.axpy (-α) x y := by simp

example (x : Vec n) : blas%(x := -x) = Vec.scal (-1) x := by simp

-- A block is its routine calls in order, and a block of one statement is its call.
example (x y : Vec n) :
    (blas% do
      y := α • x + y
      y := β • y) = Vec.scal β (Vec.axpy α x y) := by simp

example (A : Mat m n) (x : Vec n) (y : Vec m) :
    (blas% do y := α • A * x + β • y) = Mat.gemv α A x β y := by simp

-- The specifications of the routines apply to the updates.
example (A : Mat m n) (x : Vec n) (y : Vec m) (i : Nat) (h : i < m) (hn : n ≠ 0)
    (hα : (α == 0) = false) :
    (blas%(y := α • A * x + β • y))[i] =
      Nat.fold n (fun j _ s => s + α * x[j] * A[(i, j)]) (betaMul β y[i]) := by
  simp [hn, hα]

end

/-! ## Values -/

-- `[[1, 2], [3, 4]] * [1, 1] = [3, 7]`, its transpose `[4, 6]`, and `2 * [3, 7] - [1, 1]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 1]
  let y : Vec 2 := .ofList [1, 1]
  (blas%(y := A * x)).toList == [3, 7] && (blas%(y := Aᵀ * x)).toList == [4, 6] &&
    (blas%(y := 2 • A * x + (-1) • y)).toList == [5, 13]

-- In a `do` block, `blas%` updates a mutable variable, and `A[:, j]` is a column of `A`.
#guard Id.run do
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let mut y : Vec 2 := .ofList [0, 0]
  blas% y := A[:, 1]
  blas% y += 2 • A[:, 0]
  blas% y := 3 • y
  blas% y += A * A[:, 0]
  -- `3 * ([2, 4] + 2 * [1, 3]) + [[1, 2], [3, 4]] * [1, 3]`
  return y.toList == [19, 45]

-- `y - 2 * x` and `A * x - y`, for `A = [[1, 2], [3, 4]]`, `x = [1, 1]` and `y = [5, 5]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 1]
  let y : Vec 2 := .ofList [5, 5]
  (blas%(y -= 2 • x)).toList == [3, 3] && (blas%(y := A * x - y)).toList == [-2, 2]

-- `2 • x + 3 • y` and `y := 2 • x`, by `axpby`, and `Aᵀ * B` by `gemmTN`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 2]
  let y : Vec 2 := .ofList [10, 20]
  let C : Mat 2 2 := .ofPMat ⟨.ofList [0, 0, 0, 0], by decide⟩
  (blas%(y := 2 • x + 3 • y)).toList == [32, 64] && (blas%(y := 2 • x)).toList == [2, 4] &&
    (blas%(C := Aᵀ * A)).toList == [10, 14, 14, 20]

-- A block updates its mutable variables in order, with `blas%` once.
#guard Id.run do
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let mut x : Vec 2 := .ofList [1, 1]
  let mut y : Vec 2 := .ofList [0, 0]
  blas% do
    y := A * x
    x := 2 • y - x
    y -= A[:, 0]
  -- `y = [3, 7]`, then `x = [5, 13]`, then `y = [2, 4]`.
  return x.toList == [5, 13] && y.toList == [2, 4]

-- As a term, a block is the new value of its last target.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 1]
  let y : Vec 2 := .ofList [0, 0]
  let z := blas% do
    y := A * x
    y += x
  z.toList == [4, 8] && y.toList == [0, 0]

-- `C := A * B + C`, for `A = [[1, 2], [3, 4]]`, `B = I` and `C = [[1, 1], [1, 1]]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := .ofPMat ⟨.ofList [1, 0, 0, 1], by decide⟩
  let C : Mat 2 2 := .ofPMat ⟨.ofList [1, 1, 1, 1], by decide⟩
  (blas%(C += A * B)).toList == [2, 4, 3, 5]

-- `[[2, 0], [1, 1]]⁻¹ * [2, 3] = [1, 2]`, from the lower triangle of `[[2, 9], [1, 1]]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [2, 1, 9, 1], by decide⟩
  let x : Vec 2 := .ofList [2, 3]
  (blas%(x := A.lower⁻¹ * x)).toList == [1, 2]

-- `[[2, 1], [0, 1]]⁻¹ * [4, 2] = [1, 2]`, by the transpose of the lower triangle of
-- `[[2, 9], [1, 1]]`, and `[[2, 9], [0, 1]] * [1, 1] = [11, 1]`, by its upper triangle.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [2, 1, 9, 1], by decide⟩
  let x : Vec 2 := .ofList [4, 2]
  let y : Vec 2 := .ofList [1, 1]
  (blas%(x := A.lowerᵀ⁻¹ * x)).toList == [1, 2] && (blas%(y := A.upper * y)).toList == [11, 1]

-- `[[2, 1], [1, 1]] * [1, 2] = [4, 3]`, the symmetric matrix of the lower triangle.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [2, 1, 9, 1], by decide⟩
  let x : Vec 2 := .ofList [1, 2]
  let y : Vec 2 := .ofList [0, 0]
  (blas%(y := A.symLower * x)).toList == [4, 3]

-- `[1, 2] * [3, 4]ᵀ = [[3, 4], [6, 8]]`, by `ger`.
#guard
  let x : Vec 2 := .ofList [1, 2]
  let y : Vec 2 := .ofList [3, 4]
  let A : Mat 2 2 := .ofPMat ⟨.ofList [0, 0, 0, 0], by decide⟩
  (blas%(A += x * yᵀ)).toList == [3, 6, 4, 8]

-- `A * Aᵀ = [[5, 11], [11, 25]]` for `A = [[1, 2], [3, 4]]`, over the lower triangle of `C` only,
-- and `x * yᵀ + y * xᵀ = [[0, 1], [1, 0]]`, over the upper triangle only.
#guard Id.run do
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 0]
  let y : Vec 2 := .ofList [0, 1]
  let mut C : Mat 2 2 := .ofPMat ⟨.ofList [7, 7, 7, 7], by decide⟩
  let mut D : Mat 2 2 := .ofPMat ⟨.ofList [0, 0, 0, 0], by decide⟩
  blas% do
    C.lower := A * Aᵀ
    D.upper += x * yᵀ + y * xᵀ
  return C.toList == [5, 11, 7, 25] && D.toList == [0, 0, 1, 0]

/-! ## In place

An update compiles to its routine's call, so it updates its target in place when the target's
array is not shared. -/

/-- The address of the array of `x`, with `x`, taken before `x` goes on to an update. -/
@[noinline] def withAddr (x : Vec n) : USize × Vec n := (BLASTest.addr x.data, x)

/--
`gemv`, `gemvT`, `axpy`, `trsv`, `trsvT`, `trmvT` and `symv` by `blas%` update `y` in place.
-/
def inPlace (m : Nat) : Bool := Id.run do
  let A : Mat m m := .ofFn fun i j => ((i.val * 7 + j.val * 13) % 11).toFloat - 5
  let x : Vec m := .ofFn fun i => (i.val % 9).toFloat - 4
  let (p, y) := withAddr (.ofFn fun i => (i.val % 5).toFloat)
  let mut y := y
  blas% y := 2 • A * x + 3 • y
  blas% y += 2 • Aᵀ * x
  blas% y += 2 • x
  blas% y := A.unitLower⁻¹ * y
  blas% y := A.unitUpperᵀ⁻¹ * y
  blas% y := A.upperᵀ * y
  blas% y += A.symLower * x
  return BLASTest.addr y.data == p

#guard inPlace 8

/-- The same updates as one block, as a term. -/
def inPlaceBlock (m : Nat) : Bool :=
  let A : Mat m m := .ofFn fun i j => ((i.val * 7 + j.val * 13) % 11).toFloat - 5
  let x : Vec m := .ofFn fun i => (i.val % 9).toFloat - 4
  let (p, y) := withAddr (.ofFn fun i => (i.val % 5).toFloat)
  let z := blas% do
    y := 2 • A * x + 3 • y
    y += 2 • Aᵀ * x
    y += 2 • x
    y := A.unitLower⁻¹ * y
    y := A.unitUpperᵀ⁻¹ * y
    y := A.upperᵀ * y
    y += A.symLower * x
  BLASTest.addr z.data == p

#guard inPlaceBlock 8

/-- The address of the array of `C`, with `C`, taken before `C` goes on to an update. -/
@[noinline] def withMatAddr (C : Mat m n) : USize × Mat m n := (BLASTest.addr C.data, C)

/--
`ger`, `trmm`, `trsmT`, `symm`, and `syrk`, `syr2k` and `gemmtr` over a triangle, by `blas%`,
update `C` in place.
-/
def inPlaceMat (m : Nat) : Bool := Id.run do
  let A : Mat m m := .ofFn fun i j => ((i.val * 7 + j.val * 13) % 11).toFloat - 5
  let B : Mat m m := .ofFn fun i j => ((i.val * 5 + j.val * 3) % 7).toFloat - 3
  let x : Vec m := .ofFn fun i => (i.val % 9).toFloat - 4
  let (p, C) := withMatAddr (m := m) (.ofFn fun i j => ((i.val + j.val) % 5).toFloat)
  let mut C := C
  blas% do
    C += 2 • x * xᵀ
    C := 2 • A.lower * C
    C := A.unitUpperᵀ⁻¹ * C
    C := A.symLower * B + 3 • C
    C.lower := 2 • A * Aᵀ + C.lower
    C.upper += A * Bᵀ + B * Aᵀ
    C.lower -= Aᵀ * B
  return BLASTest.addr C.data == p

#guard inPlaceMat 8

/-! ## Updates that no single routine computes -/

/--
error: blas%: no single BLAS routine computes this update of `y`
-/
#guard_msgs in
example (A : Mat 2 2) (x z y : Vec 2) : Vec 2 := blas%(y := A * x - z)

/--
error: blas%: no single BLAS routine computes this update of `y`
-/
#guard_msgs in
example (x z y : Vec 2) : Vec 2 := blas%(y := (2 : Float) • x + (3 : Float) • z)

/--
error: blas%: no single BLAS routine computes a product of three factors
-/
#guard_msgs in
example (A B : Mat 2 2) (x y : Vec 2) : Vec 2 := blas%(y := A * B * x)

/--
error: blas%: no single BLAS routine computes this factor; write it with a separate update first
-/
#guard_msgs in
example (A : Mat 2 2) (x z y : Vec 2) : Vec 2 := blas%(y := A * (x - z))

/--
error: blas%: no `do` or nested `blas%` in a statement; bind the value with `let` first
-/
#guard_msgs in
example (A : Mat 2 2) (x y : Vec 2) : Vec 2 := blas%(y := A * blas%(x := A * x) + y)

/--
error: blas%: no `do` or nested `blas%` in a statement; bind the value with `let` first
-/
#guard_msgs in
example (x y : Vec 2) : Vec 2 := blas%(y := (Id.run do return (2 : Float)) • x + y)

/--
error: blas%: `y` occurs twice; combine its scalars
-/
#guard_msgs in
example (x y : Vec 2) : Vec 2 := blas%(y := x + y + y)

/--
error: blas%: no single BLAS routine computes this update of `C`
-/
#guard_msgs in
example (A B : Mat 2 2) (C : Mat 2 2) : Mat 2 2 := blas%(C := A * Bᵀ + B * Aᵀ)

/--
error: blas%: no single BLAS routine computes this update of `C.lower`
-/
#guard_msgs in
example (A B : Mat 2 2) (C : Mat 2 2) : Mat 2 2 :=
  blas%(C.lower := (2 : Float) • A * Bᵀ + B * Aᵀ)

-- A product over one of its operands needs a triangle: `gemv` doesn't update its operand.
/--
error: failed to synthesize instance of type class
  MulIn (Mat 2 2) (Vec 2)

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (A : Mat 2 2) (x : Vec 2) : Vec 2 := blas%(x := A * x)
