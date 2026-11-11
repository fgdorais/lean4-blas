/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# Vectors

`Vec n` is a vector of `n` floats, stored contiguously in a `Float64Array`. Its size is part of
its type, so the routines need no size checks.
-/

open ScalarArray

namespace BLAS.Float64

/-- A vector of `n` floats, stored contiguously in a `Float64Array`. -/
public structure Vec (n : Nat) where
  /-- The elements. -/
  data : Float64Array
  /-- The array has `n` elements. -/
  size_data : data.size = n

namespace Vec

variable {n : Nat}

public instance : GetElem (Vec n) Nat Float fun _ i => i < n where
  getElem x i h := x.data[i]'(by rw [x.size_data]; exact h)

public theorem getElem_def (x : Vec n) (i : Nat) (h : i < n) :
    x[i] = x.data[i]'(by rw [x.size_data]; exact h) := rfl

/-- The element at the `USize` index `i`. It compiles to an inline load. -/
@[inline] public def uget (x : Vec n) (i : USize) (h : i.toNat < n) : Float :=
  x.data.uget i (by rw [x.size_data]; exact h)

@[simp] public theorem uget_eq_getElem (x : Vec n) (i : USize) (h : i.toNat < n) :
    x.uget i h = x[i.toNat] := by
  simp [uget, getElem_def]

/-- The vector with the elements `f i`. -/
public def ofFn (f : Fin n → Float) : Vec n := ⟨.ofFn f, by simp⟩

@[simp] public theorem getElem_ofFn (f : Fin n → Float) (i : Nat) (h : i < n) :
    (ofFn f)[i] = f ⟨i, h⟩ := by
  simp [getElem_def, ofFn]

/-- The vector with the elements of `l`, of length `n`. -/
public def ofList (l : List Float) (h : l.length = n := by simp) : Vec n :=
  ofFn fun i => l[i.val]'(by rw [h]; exact i.isLt)

/-- The elements as a list. -/
public def toList (x : Vec n) : List Float := x.data.toList

end Vec

end BLAS.Float64
