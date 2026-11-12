/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# Vectors

`Vec n` is a vector of `n` floats, stored in a `Float64Array` with an offset and a stride, as in
the reference BLAS: element `i` is at the index `off + inc * i`. Its size is part of its type, so
the routines need no size checks. The other elements of the array are not part of the vector, so a
vector can be a row or a column of a matrix, and the routines that update a vector leave them
unchanged.
-/

open ScalarArray

namespace BLAS.Float64

/--
`(x + y * z).toNat = x.toNat + y.toNat * z.toNat` when the result doesn't wrap around: the index
of the element `z` of a stride `y` at `x`.
-/
public theorem USize.toNat_add_mul_of_lt {x y z : USize}
    (h : x.toNat + y.toNat * z.toNat < USize.size) :
    (x + y * z).toNat = x.toNat + y.toNat * z.toNat := by
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_add, USize.toNat_mul, Nat.mod_eq_of_lt (a := y.toNat * z.toNat) (by omega),
    Nat.mod_eq_of_lt h]

/--
A vector of `n` floats, stored in a `Float64Array` from the index `off`, with the stride `inc`.
The stride is positive, unless the vector has at most one element, so that its elements are at
distinct indices.
-/
public structure Vec (n : Nat) where
  /-- The array that holds the elements. -/
  data : Float64Array
  /-- The index of the first element. -/
  off : USize
  /-- The distance between two consecutive elements. -/
  inc : USize
  /-- The stride is positive, unless the vector has at most one element. -/
  inc_pos : 0 < inc.toNat ∨ n ≤ 1
  /-- The last element is in the array. -/
  bound : n = 0 ∨ off.toNat + inc.toNat * (n - 1) < data.size

namespace Vec

variable {n : Nat}

/-- The index `off + inc * i` of element `i < n` is in the array. -/
public theorem index_lt (x : Vec n) {i : Nat} (h : i < n) :
    x.off.toNat + x.inc.toNat * i < x.data.size := by
  have : x.inc.toNat * i ≤ x.inc.toNat * (n - 1) := Nat.mul_le_mul_left _ (by omega)
  rcases x.bound with h' | h' <;> omega

/-- A vector has at most as many elements as its array. -/
public theorem le_size (x : Vec n) : n ≤ x.data.size := by
  rcases Nat.lt_or_ge n 2 with h | h
  · rcases Nat.lt_or_ge n 1 with h' | h'
    · omega
    · have := x.index_lt (i := 0) (by omega); omega
  · have hinc : 0 < x.inc.toNat := by rcases x.inc_pos with h' | h' <;> omega
    have : n - 1 ≤ x.inc.toNat * (n - 1) := Nat.le_mul_of_pos_left _ hinc
    have := x.index_lt (i := n - 1) (by omega)
    omega

/-- The steps `i < n` of a vector are at distinct indices: `inc > 0`, or `i = 0`. -/
public theorem inc_pos_of_lt (x : Vec n) {i : Nat} (h : i < n) : 0 < x.inc.toNat ∨ i = 0 := by
  rcases x.inc_pos with h' | h' <;> omega

/-- The `USize` index of element `i < n`, in an array of `USize` size, doesn't wrap around. -/
public theorem toNat_index (x : Vec n) (hs : x.data.size < USize.size) {i : USize}
    (h : i.toNat < n) : (x.off + x.inc * i).toNat = x.off.toNat + x.inc.toNat * i.toNat :=
  USize.toNat_add_mul_of_lt (by have := x.index_lt h; omega)

/-- The `USize` index of element `i < n` is in the array. -/
public theorem toNat_index_lt (x : Vec n) (hs : x.data.size < USize.size) {i : USize}
    (h : i.toNat < n) : (x.off + x.inc * i).toNat < x.data.size := by
  rw [x.toNat_index hs h]; exact x.index_lt h

public instance : GetElem (Vec n) Nat Float fun _ i => i < n where
  getElem x i h := x.data[x.off.toNat + x.inc.toNat * i]'(x.index_lt h)

public theorem getElem_def (x : Vec n) (i : Nat) (h : i < n) :
    x[i] = x.data[x.off.toNat + x.inc.toNat * i]'(x.index_lt h) := rfl

/--
The element at the `USize` index `i`, in a vector whose array has a `USize` size, as every array
in memory does. It compiles to an inline load.
-/
@[inline] public def uget (x : Vec n) (hs : x.data.size < USize.size) (i : USize)
    (h : i.toNat < n) : Float :=
  x.data.uget (x.off + x.inc * i) (x.toNat_index_lt hs h)

@[simp] public theorem uget_eq_getElem (x : Vec n) (hs : x.data.size < USize.size) (i : USize)
    (h : i.toNat < n) : x.uget hs i h = x[i.toNat] := by
  simp only [uget, Float64Array.uget_eq_getElem, getElem_def, x.toNat_index hs h]

/-- The contiguous vector of the elements of `a`, from the index `0`. -/
@[expose] public def ofArray (a : Float64Array) (h : a.size = n) : Vec n where
  data := a
  off := 0
  inc := 1
  inc_pos := Or.inl (by simp)
  bound := by
    rcases Nat.eq_zero_or_pos n with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by simp; omega)

@[simp] public theorem data_ofArray (a : Float64Array) (h : a.size = n) : (ofArray a h).data = a :=
  rfl

@[simp] public theorem getElem_ofArray (a : Float64Array) (h : a.size = n) (i : Nat) (hi : i < n) :
    (ofArray a h)[i] = a[i]'(by omega) := by
  simp [getElem_def, ofArray]

/--
The vector of `n` elements of `a` from the index `off` with the stride `inc`, if they are in `a`
and the stride is positive or `n ≤ 1`.
-/
public def ofStride? (a : Float64Array) (off inc : USize) : Option (Vec n) :=
  if h : (0 < inc.toNat ∨ n ≤ 1) ∧ (n = 0 ∨ off.toNat + inc.toNat * (n - 1) < a.size) then
    some ⟨a, off, inc, h.1, h.2⟩
  else none

/-- The contiguous vector with the elements `f i`. -/
public def ofFn (f : Fin n → Float) : Vec n := ofArray (.ofFn f) (by simp)

@[simp] public theorem getElem_ofFn (f : Fin n → Float) (i : Nat) (h : i < n) :
    (ofFn f)[i] = f ⟨i, h⟩ := by
  simp [ofFn]

/-- The contiguous vector with the elements of `l`, of length `n`. -/
public def ofList (l : List Float) (h : l.length = n := by simp) : Vec n :=
  ofFn fun i => l[i.val]'(by rw [h]; exact i.isLt)

/-- The elements as a list. -/
public def toList (x : Vec n) : List Float := List.ofFn fun i : Fin n => x[i.val]

@[simp] public theorem length_toList (x : Vec n) : x.toList.length = n := by
  simp [toList]

@[simp] public theorem getElem_toList (x : Vec n) (i : Nat) (h : i < x.toList.length) :
    x.toList[i] = x[i]'(by simpa using h) := by
  simp [toList]

/-- Two vectors with the same elements have the same list of elements. -/
public theorem toList_eq {x y : Vec n} (h : ∀ i (hi : i < n), x[i] = y[i]) :
    x.toList = y.toList := by
  apply List.ext_getElem (by simp)
  intro i _ _
  simp only [getElem_toList]
  exact h i (by simpa using ‹i < x.toList.length›)

end Vec

end BLAS.Float64
