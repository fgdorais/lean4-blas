/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Vec
public import BLAS.Float64.Loop
public import ScalarArray.InPlaceSyntax

/-!
# Level 1

Vector operations.

Each routine has a kernel on `Float64Array`, which runs an in-place loop when the array's size fits
in a `USize`, as it does for every array in memory, and its model otherwise, so that its
specification needs no hypothesis on the size.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Kernel

/-- `α * x + y`, written over `y`. -/
public def axpy (α : Float) (x y : Float64Array) (h : x.size = y.size) : Float64Array :=
  if hs : y.size < USize.size then
    (inplace y do
      for j in 0...y.usize do
        y[j] := α * x[j] + y[j]).2
  else mapRange y 0 y.size fun j v => α * x[j]! + v

public theorem axpy_eq (α : Float) (x y : Float64Array) (h : x.size = y.size) :
    axpy α x y h = mapRange y 0 y.size fun j v => α * x[j]! + v := by
  unfold axpy
  split
  · rename_i hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [run_forInFrom_map (G := fun j v => α * x[j]! + v)]
    · simp only [Tail.run_done, toNat_usize_of_lt y hs, USize.toNat_zero]
    · intro j hj v
      rw [toNat_usize_of_lt y hs] at hj
      simp [getElem!_pos x j.toNat (by omega)]
  · rfl

end Kernel

namespace Vec

variable {n : Nat}

/--
`axpy α x y` is `α * x + y`. It updates `y` in place when `y` is not shared.
-/
public def axpy (α : Float) (x y : Vec n) : Vec n :=
  ⟨Kernel.axpy α x.data y.data (x.size_data.trans y.size_data.symm), by
    rw [Kernel.axpy_eq]; simp [y.size_data]⟩

@[simp] public theorem getElem_axpy (α : Float) (x y : Vec n) (i : Nat) (h : i < n) :
    (axpy α x y)[i] = α * x[i] + y[i] := by
  have := x.size_data; have := y.size_data
  simp only [getElem_def, axpy, Kernel.axpy_eq, getElem_mapRange]
  simp [y.size_data, h, getElem!_pos x.data i (by omega)]

end Vec

end BLAS.Float64
