/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
import BLASTest.Util
meta import BLAS
meta import BLASTest.Util

open BLAS.Float32

/-- An `m × n` matrix of small integers computed from the indices and the seed `s`. -/
def mat (m n : Nat) (s : Nat := 0) : Mat m n :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat32 - 5

/-- The elements of `gemmEntry`, column after column. -/
def gemmModelList (α : Float32) (A : Mat m k) (B : Mat k n) (β : Float32) (C : Mat m n) :
    List Float32 :=
  (List.ofFn fun j : Fin n => List.ofFn fun i : Fin m =>
    Mat.gemmEntry α A B β C i.val j.val i.isLt j.isLt).flatten

/--
The address of the array of `A`, with `A`. It is not inlined, so the address is taken before `A`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (A : Mat m n) : USize × Mat m n := (BLASTest.addr A.data, A)

/-- Whether `gemm` computes its model exactly, for these shapes. -/
def gemmMatchesModel (m n k : Nat) (α β : Float32) : Bool :=
  let A := mat m k 1
  let B := mat k n 2
  let C := mat m n 3
  (Mat.gemm α A B β C).toList == gemmModelList α A B β C

/-! ## `gemm` -/

-- `[[1, 2], [3, 4]] * [[5, 6], [7, 8]] = [[19, 22], [43, 50]]`, in column-major order.
#guard
  let A : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := Mat.ofPMat ⟨.ofList [5, 7, 6, 8], by decide⟩
  let C : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 1, 1, 1], by decide⟩
  (Mat.gemm 1 A B 0 C).toList == [19, 43, 22, 50] &&
    (Mat.gemm 2 A B 1 C).toList == [39, 87, 45, 101]

-- A `2 × 3` times a `3 × 1`.
#guard
  let A : Mat 2 3 := Mat.ofPMat ⟨.ofList [1, 4, 2, 5, 3, 6], by decide⟩
  let B : Mat 3 1 := Mat.ofPMat ⟨.ofList [1, 0, -1], by decide⟩
  let C : Mat 2 1 := Mat.ofPMat ⟨.ofList [10, 20], by decide⟩
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

#guard gemmMatchesModel 5 4 3 0 0.5
#guard gemmMatchesModel 5 4 3 1.5 0
#guard gemmMatchesModel 5 4 3 0 0

-- As in the reference BLAS, `β = 0` sets `C` to `0` without reading it, so a `NaN` in `C` goes.
#guard
  let C : Mat 1 1 := Mat.ofPMat ⟨.ofList [0 / 0], by decide⟩
  (Mat.gemm 1 (mat 1 1) (mat 1 1) 0 C).toList == [(mat 1 1)[(0, 0)] * (mat 1 1)[(0, 0)]] &&
    (Mat.gemmBlocked 1 (mat 1 1) (mat 1 1) 0 C).toList == [(mat 1 1)[(0, 0)] * (mat 1 1)[(0, 0)]]

-- `α = 0` only scales `C`, without reading `A` or `B`.
#guard
  let A : Mat 1 1 := .ofFn fun _ _ => 0 / 0
  let C : Mat 1 1 := .ofFn fun _ _ => 3
  (Mat.gemm 0 A A 2 C).toList == [6] && (Mat.gemmBlocked 0 A A 0 C).toList == [0]

/-- Whether `gemm` updates an unshared `C` in place. -/
def gemmInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (mat m m 3)
  BLASTest.addr (Mat.gemm 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmInPlace 8

-- A shared `C` is copied, and keeps its elements.
#guard
  let C := mat 4 4 3
  let D := Mat.gemm 1 (mat 4 4 1) (mat 4 4 2) 1 C
  C.toList == (mat 4 4 3).toList && D.toList == gemmModelList 1 (mat 4 4 1) (mat 4 4 2) 1 C

/-! ## `gemmBlocked` -/

/-- Whether `gemmBlocked` computes the same matrix as `gemm`, for these shapes. -/
def gemmBlockedMatches (m n k : Nat) (α β : Float32) : Bool :=
  let A := mat m k 1
  let B := mat k n 2
  let C := mat m n 3
  let D := (Mat.gemmBlocked α A B β C).data
  let E := (Mat.gemm α A B β C).data
  D.size == E.size && (List.range D.size).all fun i => D[i]! == E[i]!

#guard
  let A : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := Mat.ofPMat ⟨.ofList [5, 7, 6, 8], by decide⟩
  (Mat.gemmBlocked 1 A B 0 (mat 2 2)).toList == [19, 43, 22, 50]

-- Odd shapes cover the last column, the leftover terms and the last row block.
#guard gemmBlockedMatches 5 4 3 1.5 0.5
#guard gemmBlockedMatches 1 1 1 2 3
#guard gemmBlockedMatches 17 9 13 (-0.25) 2
#guard gemmBlockedMatches 63 7 130 1 1
#guard gemmBlockedMatches 257 3 129 0.5 (-1)
#guard gemmBlockedMatches 300 5 260 1.25 0.75

-- Empty shapes.
#guard gemmBlockedMatches 0 3 2 1 1
#guard gemmBlockedMatches 3 0 2 1 1
#guard gemmBlockedMatches 3 2 0 1 2

/-- Whether `gemmBlocked` updates an unshared `C` in place. -/
def gemmBlockedInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (mat m m 3)
  BLASTest.addr (Mat.gemmBlocked 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmBlockedInPlace 8
#guard gemmBlockedInPlace 33

-- A shared `C` is copied, and keeps its elements.
#guard
  let C := mat 4 4 3
  let D := Mat.gemmBlocked 1 (mat 4 4 1) (mat 4 4 2) 1 C
  C.toList == (mat 4 4 3).toList && D.toList == (Mat.gemm 1 (mat 4 4 1) (mat 4 4 2) 1 C).toList

/-! ## Matrices with an offset and a leading dimension -/

/--
The matrix `mat m n s` at the offset `off` with the leading dimension `ld`, in an array whose
other elements are `1e9 + 0.5`, a value that no test computes.
-/
def matLd (m n off ld : Nat) (s : Nat := 0) : Mat m n :=
  let a := ScalarArray.Float32Array.ofFn (n := off + ld * n) fun p =>
    let q := p.val - off
    if off ≤ p.val ∧ q % ld < m then ((q % ld * 7 + q / ld * 13 + s) % 11).toFloat32 - 5 else 1e9 + 0.5
  (Mat.ofLd? a off ld).getD (mat m n s)

/-- The number of elements `1e9 + 0.5` in the array of `A`: those outside a matrix of `matLd`. -/
def outside (A : Mat m n) : Nat := A.data.toList.countP (· == 1e9 + 0.5)

#guard (matLd 3 4 5 7 1).toList == (mat 3 4 1).toList
#guard (matLd 3 4 5 7).data.size == 33
#guard outside (matLd 3 4 5 7) == 33 - 12
#guard ((Mat.ofLd? (m := 3) (n := 2) (.ofList [1, 2, 3, 4, 5]) 0 2).map Mat.toList).isNone
#guard ((Mat.ofLd? (m := 2) (n := 2) (.ofList [1, 2, 3, 4, 5]) 1 2).map Mat.toList) ==
  some [2, 3, 4, 5]

-- Rows and columns are vectors.
#guard ((matLd 3 4 5 7 1).col 2 (by decide)).toList == [(mat 3 4 1)[(0, 2)], (mat 3 4 1)[(1, 2)],
  (mat 3 4 1)[(2, 2)]]
#guard ((matLd 3 4 5 7 1).row 1 (by decide)).toList ==
  (List.range 4).map fun j => (mat 3 4 1).toList[1 + 3 * j]!

/-- Whether `gemm` and `gemmBlocked` on matrices with offsets and leading dimensions compute the
same elements as on packed ones, and leave the rest of `C`'s array. -/
def gemmLdMatches (m n k : Nat) (α β : Float32) : Bool :=
  let A := matLd m k 3 (m + 2) 1
  let B := matLd k n 1 (k + 1) 2
  let C := matLd m n 4 (m + 3) 3
  let D := Mat.gemm α A B β C
  let E := Mat.gemmBlocked α A B β C
  D.toList == gemmModelList α (mat m k 1) (mat k n 2) β (mat m n 3) &&
    E.toList == D.toList && outside D == outside C && outside E == outside C &&
    D.data.size == C.data.size

#guard gemmLdMatches 5 4 3 1.5 0.5
#guard gemmLdMatches 17 9 13 (-0.25) 2
#guard gemmLdMatches 257 3 129 0.5 (-1)
#guard gemmLdMatches 0 3 2 1 1
#guard gemmLdMatches 3 0 2 1 1
#guard gemmLdMatches 3 2 0 1 2

/-- Whether `gemm` updates the array of an unshared `C` with a leading dimension in place. -/
def gemmLdInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (matLd m m 2 (m + 1) 3)
  BLASTest.addr (Mat.gemm 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmLdInPlace 8
