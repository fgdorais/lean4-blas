/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
import BLASTest.Util
meta import BLAS
meta import BLASTest.Util

open BLAS.Float64

/-- An `m × n` matrix of small integers computed from the indices and the seed `s`. -/
def mat (m n : Nat) (s : Nat := 0) : Mat m n :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat - 5

/-- Whether `gemm` computes its model exactly, for these shapes. -/
def gemmMatchesModel (m n k : Nat) (α β : Float) : Bool :=
  let A := mat m k 1
  let B := mat k n 2
  let C := mat m n 3
  (Mat.gemm α A B β C).toList == (Mat.gemmModel α A B β C).toList

/-! ## `gemm` -/

-- `[[1, 2], [3, 4]] * [[5, 6], [7, 8]] = [[19, 22], [43, 50]]`, in column-major order.
#guard
  let A : Mat 2 2 := ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := ⟨.ofList [5, 7, 6, 8], by decide⟩
  let C : Mat 2 2 := ⟨.ofList [1, 1, 1, 1], by decide⟩
  (Mat.gemm 1 A B 0 C).toList == [19, 43, 22, 50] &&
    (Mat.gemm 2 A B 1 C).toList == [39, 87, 45, 101]

-- A `2 × 3` times a `3 × 1`.
#guard
  let A : Mat 2 3 := ⟨.ofList [1, 4, 2, 5, 3, 6], by decide⟩
  let B : Mat 3 1 := ⟨.ofList [1, 0, -1], by decide⟩
  let C : Mat 2 1 := ⟨.ofList [10, 20], by decide⟩
  (Mat.gemm 1 A B (-1) C).toList == [-12, -22]

#guard gemmMatchesModel 5 4 3 1.5 0.5
#guard gemmMatchesModel 1 1 1 2 3
#guard gemmMatchesModel 17 9 13 (-0.25) 2
#guard gemmMatchesModel 32 33 31 1 1

-- Empty shapes: with `k = 0`, `gemm` is `β * C`.
#guard gemmMatchesModel 0 3 2 1 1
#guard gemmMatchesModel 3 0 2 1 1
#guard gemmMatchesModel 3 2 0 1 2
#guard (Mat.gemm 1 (mat 3 0) (mat 0 2) 2 (mat 3 2)).toList == (mat 3 2).toList.map (2 * ·)

-- Unlike the reference BLAS, `β = 0` keeps a `NaN` of `C`.
#guard
  let C : Mat 1 1 := ⟨.ofList [0 / 0], by decide⟩
  (Mat.gemm 1 (mat 1 1) (mat 1 1) 0 C).toList.all (·.isNaN)

/-- Whether `gemm` updates an unshared `C` in place. -/
def gemmInPlace (m : Nat) : Bool :=
  let C := mat m m 3
  let p := BLASTest.addr C.data
  BLASTest.addr (Mat.gemm 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmInPlace 8

-- A shared `C` is copied, and keeps its elements.
#guard
  let C := mat 4 4 3
  let D := Mat.gemm 1 (mat 4 4 1) (mat 4 4 2) 1 C
  C.toList == (mat 4 4 3).toList && D.toList == (Mat.gemmModel 1 (mat 4 4 1) (mat 4 4 2) 1 C).toList
