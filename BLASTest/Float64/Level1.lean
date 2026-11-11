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
  let y := ramp n
  let p := BLASTest.addr y.data
  let z := Vec.axpy 2 (ramp n 3) y
  BLASTest.addr z.data == p

#guard axpyInPlace 8

-- A shared `y` is copied, and keeps its elements.
#guard
  let y := ramp 8
  let z := Vec.axpy 2 (ramp 8) y
  y.toList == (ramp 8).toList && z.toList == (ramp 8 3).toList
