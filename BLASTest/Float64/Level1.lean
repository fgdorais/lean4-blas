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

/-- The vector `[0, 1, …, n - 1]` scaled by `c`. -/
def ramp (n : Nat) (c : Float := 1) : Vec n := .ofFn fun i => c * i.val.toFloat

/--
The address of the array of `x`, with `x`. It is not inlined, so the address is taken before `x`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (x : Vec n) : USize × Vec n := (BLASTest.addr x.data, x)

/-! ## `axpy` -/

#guard (Vec.axpy 2 (.ofList (n := 3) [1, 2, 3]) (.ofList (n := 3) [10, 20, 30])).toList == [12, 24, 36]
#guard (Vec.axpy 0 (.ofList (n := 3) [1, 2, 3]) (.ofList (n := 3) [10, 20, 30])).toList == [10, 20, 30]
#guard (Vec.axpy (-1) (ramp 4) (ramp 4)).toList == [0, 0, 0, 0]
#guard (Vec.axpy 3 (ramp 0) (ramp 0)).toList == []

-- Every element, past 16 bits of index.
#guard
  let n := 70000
  let z := Vec.axpy 2 (ramp n) (ramp n 0.5)
  (List.range n).all fun i => z.toList[i]! == 2.5 * i.toFloat

-- Special values propagate as in `α * x[i] + y[i]`.
#guard
  let inf : Float := 1 / 0
  let z := Vec.axpy 1 (.ofList (n := 3) [inf, -inf, 1]) (.ofList (n := 3) [1, inf, 0 / 0])
  match z.toList with
  | [a, b, c] => a == inf && b.isNaN && c.isNaN
  | _ => false

/-- Whether `axpy` updates an unshared `y` in place. -/
def axpyInPlace (n : Nat) : Bool :=
  let (p, y) := withAddr (ramp n)
  let z := Vec.axpy 2 (ramp n 3) y
  BLASTest.addr z.data == p

#guard axpyInPlace 8

-- A shared `y` is copied, and keeps its elements.
#guard
  let y := ramp 8
  let z := Vec.axpy 2 (ramp 8) y
  y.toList == (ramp 8).toList && z.toList == (ramp 8 3).toList

/-! ## `scal` -/

#guard (Vec.scal 2 (.ofList (n := 3) [1, -2, 3])).toList == [2, -4, 6]
#guard (Vec.scal 3 (ramp 0)).toList == []
#guard
  let n := 70000
  let z := Vec.scal 0.5 (ramp n)
  (List.range n).all fun i => z.toList[i]! == 0.5 * i.toFloat

/-- Whether `scal` updates an unshared `x` in place. -/
def scalInPlace (n : Nat) : Bool :=
  let (p, x) := withAddr (ramp n)
  BLASTest.addr (Vec.scal 2 x).data == p

#guard scalInPlace 8

#guard
  let x := ramp 8
  let z := Vec.scal 2 x
  x.toList == (ramp 8).toList && z.toList == (ramp 8 2).toList

/-! ## `copy` and `swap` -/

#guard (Vec.copy (ramp 5 2) (ramp 5)).toList == (ramp 5 2).toList
#guard (Vec.copy (ramp 0) (ramp 0)).toList == []

/-- Whether `copy` writes into an unshared `y`. -/
def copyInPlace (n : Nat) : Bool :=
  let (p, y) := withAddr (ramp n)
  BLASTest.addr (Vec.copy (ramp n 2) y).data == p

#guard copyInPlace 8

#guard
  let y := ramp 8
  let z := Vec.copy (ramp 8 2) y
  y.toList == (ramp 8).toList && z.toList == (ramp 8 2).toList

#guard
  let (a, b) := Vec.swap (ramp 3) (ramp 3 2)
  a.toList == [0, 2, 4] && b.toList == [0, 1, 2]

/-! ## Reductions -/

#guard Vec.dot (.ofList (n := 3) [1, 2, 3]) (.ofList (n := 3) [4, 5, 6]) == 32
#guard Vec.dot (ramp 0) (ramp 0) == 0
#guard Vec.asum (.ofList (n := 3) [-1, 2, -3]) == 6
#guard Vec.asum (ramp 0) == 0
#guard Vec.nrm2 (.ofList (n := 2) [3, -4]) == 5
#guard Vec.nrm2 (ramp 0) == 0

-- The sums run from the left, in the order of the spec.
#guard
  let n := 70000
  let x := ramp n 0.1
  let y := ramp n 0.3
  Vec.dot x y == (List.range n).foldl (fun s i => s + (0.1 * i.toFloat) * (0.3 * i.toFloat)) 0 &&
  Vec.asum x == (List.range n).foldl (fun s i => s + (0.1 * i.toFloat).abs) 0

#guard Vec.iamax (.ofList (n := 4) [1, -5, 5, 2]) == 1
#guard Vec.iamax (.ofList (n := 3) [0, 0, 0]) == 0
#guard Vec.iamax (ramp 0) == 0
#guard Vec.iamax (ramp 70000) == 69999
#guard Vec.iamax (.ofList (n := 3) [0 / 0, 5, 7]) == 0
#guard Vec.iamax (.ofList (n := 3) [1, 0 / 0, 7]) == 2
#guard Vec.iamax (.ofList (n := 3) [1, -1 / 0, 7]) == 1

/-! ## Strided vectors -/

/--
The vector `[0, c, …, c * (n - 1)]` at the offset `off` with the stride `inc`, in an array whose
other elements are `-1`.
-/
def strided (n off inc : Nat) (c : Float := 1) : Vec n :=
  let a := ScalarArray.Float64Array.ofFn (n := off + inc * n) fun p =>
    if off ≤ p.val ∧ (p.val - off) % inc = 0 then c * ((p.val - off) / inc).toFloat else -1
  (Vec.ofStride? a off.toUSize inc.toUSize).getD (.ofFn fun _ => 0 / 0)

/-- The number of elements `-1` in the array of `x`: those outside a strided vector. -/
def outside (x : Vec n) : Nat := x.data.toList.countP (· == -1)

#guard (strided 4 3 2).toList == [0, 1, 2, 3]
#guard (strided 4 3 2).data.size == 11
#guard outside (strided 4 3 2) == 7
#guard (Vec.ofStride? (n := 3) (.ofList [1, 2, 3, 4]) 1 2).isNone
#guard (Vec.ofStride? (n := 2) (.ofList [1, 2, 3, 4]) 1 0).isNone
#guard ((Vec.ofStride? (n := 1) (.ofList [1, 2, 3, 4]) 3 0).map Vec.toList) == some [4]

-- The updates change the elements of the vector, and only them.
#guard
  let z := Vec.axpy 2 (strided 5 1 3) (strided 5 2 2 0.5)
  z.toList == (Vec.axpy 2 (ramp 5) (ramp 5 0.5)).toList && outside z == outside (strided 5 2 2)
#guard
  let z := Vec.scal 3 (strided 5 4 3)
  z.toList == (ramp 5 3).toList && outside z == outside (strided 5 4 3)
#guard
  let z := Vec.copy (ramp 5 2) (strided 5 1 4)
  z.toList == (ramp 5 2).toList && outside z == outside (strided 5 1 4)
#guard (Vec.copy (strided 5 1 4 2) (ramp 5)).toList == (ramp 5 2).toList

-- Every element, past 16 bits of index, with a stride.
#guard
  let n := 70000
  let z := Vec.axpy 2 (strided n 0 3) (strided n 5 2 0.5)
  (List.range n).all fun i => z.toList[i]! == 2.5 * i.toFloat

/-- Whether `axpy` updates an unshared strided `y` in place. -/
def axpyInPlaceStrided (n : Nat) : Bool :=
  let (p, y) := withAddr (strided n 1 3)
  let z := Vec.axpy 2 (ramp n 3) y
  BLASTest.addr z.data == p

#guard axpyInPlaceStrided 8

#guard Vec.dot (strided 4 1 3) (strided 4 0 2 2) == Vec.dot (ramp 4) (ramp 4 2)
#guard Vec.asum (strided 4 2 5 (-1)) == 6
#guard Vec.nrm2 (strided 2 7 2 1) == 1
#guard Vec.iamax (strided 6 1 2 (-1)) == 5
