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

/-- The value of the elements outside the vectors and matrices of the tests, which no test computes. -/
def mark : Float := 1e9 + 0.5

/-- An `m × n` matrix of small integers computed from the indices and the seed `s`. -/
def mat (m n : Nat) (s : Nat := 0) : Mat m n :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat - 5

/-- A vector of small integers computed from the indices and the seed `s`. -/
def vec (n : Nat) (s : Nat := 0) : Vec n :=
  .ofFn fun i => ((i.val * 5 + s) % 9).toFloat - 4

/-- `mat m n s` at the offset `off` with the leading dimension `ld`, in an array of `mark`s. -/
def matLd (m n off ld : Nat) (s : Nat := 0) : Mat m n :=
  let a := ScalarArray.Float64Array.ofFn (n := off + ld * n) fun p =>
    let q := p.val - off
    if off ≤ p.val ∧ q % ld < m then ((q % ld * 7 + q / ld * 13 + s) % 11).toFloat - 5 else mark
  (Mat.ofLd? a off ld).getD (mat m n s)

/-- `vec n s` at the offset `off` with the stride `inc`, in an array of `mark`s. -/
def vecInc (n off inc : Nat) (s : Nat := 0) : Vec n :=
  let a := ScalarArray.Float64Array.ofFn (n := off + inc * n) fun p =>
    if off ≤ p.val ∧ (p.val - off) % inc = 0 then
      (((p.val - off) / inc * 5 + s) % 9).toFloat - 4
    else mark
  (Vec.ofStride? a off inc).getD (vec n s)

/-- The number of `mark`s in an array: the elements outside a vector or matrix of the tests. -/
def marks (a : ScalarArray.Float64Array) : Nat := a.toList.countP (· == mark)

/--
The address of the array of `x`, with `x`. It is not inlined, so the address is taken before `x`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (x : Vec n) : USize × Vec n := (BLASTest.addr x.data, x)

/-- `withAddr` for a matrix. -/
@[noinline] def withAddrMat (A : Mat m n) : USize × Mat m n := (BLASTest.addr A.data, A)

/-! ## `gemv` and `gemvT` -/

-- `[[1, 2], [3, 4]] * [1, 1] = [3, 7]`, and its transpose `[4, 6]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 1]
  let y : Vec 2 := .ofList [1, 1]
  (Mat.gemv 1 A x 0 y).toList == [3, 7] && (Mat.gemv 2 A x 1 y).toList == [7, 15] &&
    (Mat.gemvT 1 A x 0 y).toList == [4, 6] && (Mat.gemvT 2 A x (-1) y).toList == [7, 11]

/-- The spec of `gemv`, on lists. -/
def gemvList (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) : List Float :=
  List.ofFn fun i : Fin m =>
    (List.finRange n).foldl (fun s j => s + α * x[j.val] * A[(i.val, j.val)]) (β * y[i.val])

/-- The spec of `gemvT`, on lists. -/
def gemvTList (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) : List Float :=
  List.ofFn fun j : Fin n =>
    β * y[j.val] + α * (List.finRange m).foldl (fun s i => s + A[(i.val, j.val)] * x[i.val]) 0

/--
Whether `gemv` and `gemvT` match their specs, on packed operands and on operands with offsets,
strides and leading dimensions, and leave the rest of `y`'s array unchanged.
-/
def gemvMatches (m n : Nat) (α β : Float) : Bool :=
  let A := mat m n 1
  let A' := matLd m n 3 (m + 2) 1
  let ok₁ := (Mat.gemv α A (vec n 2) β (vec m 3)).toList == gemvList α A (vec n 2) β (vec m 3)
  let y := vecInc m 2 3 3
  let z := Mat.gemv α A' (vecInc n 1 2 2) β y
  let ok₂ := z.toList == gemvList α A (vec n 2) β (vec m 3) && marks z.data == marks y.data
  let ok₃ := (Mat.gemvT α A (vec m 2) β (vec n 3)).toList == gemvTList α A (vec m 2) β (vec n 3)
  let y := vecInc n 1 4 3
  let z := Mat.gemvT α A' (vecInc m 0 3 2) β y
  let ok₄ := z.toList == gemvTList α A (vec m 2) β (vec n 3) && marks z.data == marks y.data
  ok₁ && ok₂ && ok₃ && ok₄

#guard gemvMatches 5 4 1.5 0.5
#guard gemvMatches 1 1 2 3
#guard gemvMatches 17 9 (-0.25) 2
#guard gemvMatches 300 70 0.75 (-1)
#guard gemvMatches 0 3 1 1
#guard gemvMatches 3 0 1 2

-- Unlike the reference BLAS, `β = 0` keeps a `NaN` of `y`.
#guard (Mat.gemv 1 (mat 1 1) (vec 1) 0 (.ofList [0 / 0])).toList.all (·.isNaN)

/-- Whether `gemv` and `gemvT` update an unshared `y` in place. -/
def gemvInPlace (m : Nat) : Bool :=
  let (p, y) := withAddr (vecInc m 1 2)
  let (q, y') := withAddr (vecInc m 1 2 5)
  BLASTest.addr (Mat.gemv 1 (mat m m 1) (vec m 2) 1 y).data == p &&
    BLASTest.addr (Mat.gemvT 1 (mat m m 1) (vec m 2) 1 y').data == q

#guard gemvInPlace 8

/-! ## `ger` -/

-- `[1, 2] * [3, 4]ᵀ`, in column-major order.
#guard (Mat.ger (m := 2) (n := 2) 1 (.ofList [1, 2]) (.ofList [3, 4]) (.ofFn fun _ _ => 0)).toList ==
  [3, 6, 4, 8]
#guard (Mat.ger (m := 2) (n := 2) 2 (.ofList [1, 2]) (.ofList [3, 4]) (.ofFn fun _ _ => 1)).toList ==
  [7, 13, 9, 17]

/-- The spec of `ger`, on lists. -/
def gerList (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) : List Float :=
  (List.ofFn fun j : Fin n => List.ofFn fun i : Fin m =>
    A[(i.val, j.val)] + x[i.val] * (α * y[j.val])).flatten

/-- Whether `ger` matches its spec, and leaves the rest of `A`'s array unchanged. -/
def gerMatches (m n : Nat) (α : Float) : Bool :=
  let ok₁ := (Mat.ger α (vec m 2) (vec n 3) (mat m n 1)).toList ==
    gerList α (vec m 2) (vec n 3) (mat m n 1)
  let A := matLd m n 4 (m + 3) 1
  let B := Mat.ger α (vecInc m 1 2 2) (vecInc n 0 3 3) A
  ok₁ && B.toList == gerList α (vec m 2) (vec n 3) (mat m n 1) && marks B.data == marks A.data

#guard gerMatches 5 4 1.5
#guard gerMatches 1 1 2
#guard gerMatches 300 70 (-0.75)
#guard gerMatches 0 3 1
#guard gerMatches 3 0 1

/-- Whether `ger` updates an unshared `A` in place. -/
def gerInPlace (m : Nat) : Bool :=
  let (p, A) := withAddrMat (matLd m m 2 (m + 1))
  BLASTest.addr (Mat.ger 1 (vec m 2) (vec m 3) A).data == p

#guard gerInPlace 8
