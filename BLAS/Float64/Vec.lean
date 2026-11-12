/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray
public import BLAS.Internal

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
A vector of `n` floats, stored in a `Float64Array` from the index `off`, with the stride `inc`.
The stride is positive, unless the vector has at most one element, so that its elements are at
distinct indices.
-/
public structure Vec (n : Nat) where
  /-- The array that holds the elements. -/
  data : Float64Array
  /-- The index of the first element. -/
  off : Nat
  /-- The distance between two consecutive elements. -/
  inc : Nat
  /-- The stride is positive, unless the vector has at most one element. -/
  inc_pos : 0 < inc ∨ n ≤ 1
  /-- The last element is in the array. -/
  bound : n = 0 ∨ off + inc * (n - 1) < data.size

namespace Vec

variable {n : Nat}

/--
The indices `off + inc * i` of the elements, as a scalar-arrays `Stride`: element `i` is at the
index `x.stride.idx i`.
-/
@[expose] public def stride (x : Vec n) : Stride := ⟨x.off, x.inc⟩

@[simp] public theorem off_stride (x : Vec n) : x.stride.off = x.off := rfl

@[simp] public theorem inc_stride (x : Vec n) : x.stride.inc = x.inc := rfl

public theorem idx_stride (x : Vec n) (i : Nat) : x.stride.idx i = x.off + x.inc * i := rfl

/-- The `n` elements of a vector fit in its array, at distinct indices. -/
public theorem fits (x : Vec n) : x.stride.Fits n x.data.size := ⟨x.inc_pos, x.bound⟩

/-- The index `off + inc * i` of element `i < n` is in the array. -/
public theorem index_lt (x : Vec n) {i : Nat} (h : i < n) : x.off + x.inc * i < x.data.size :=
  x.fits.idx_lt h

/-- A vector has at most as many elements as its array. -/
public theorem le_size (x : Vec n) : n ≤ x.data.size := x.fits.le_size

/--
The `USize` index `off + inc * i` of element `i < n`, in an array of `USize` size, doesn't wrap
around.
-/
public theorem toNat_index (x : Vec n) (hs : x.data.size < USize.size) {i : USize}
    (h : i.toNat < n) :
    (x.off.toUSize + x.inc.toUSize * i).toNat = x.off + x.inc * i.toNat :=
  Stride.toNat_idx_toUSize x.fits hs h

/--
The `USize` index of element `j + 1 + k < n`, as the step `k` from the offset of element `j + 1`,
doesn't wrap around.
-/
public theorem toNat_index_shift (x : Vec n) (hs : x.data.size < USize.size) {j k : USize}
    (h : j.toNat + 1 + k.toNat < n) :
    (x.off.toUSize + x.inc.toUSize * (j + 1) + x.inc.toUSize * k).toNat =
      x.off + x.inc * (j.toNat + 1) + x.inc * k.toNat := by
  have hn := x.le_size
  have hjk := USize.toNat_succ_add (j := j) (k := k) (by lia)
  rw [USize.add_assoc, ← USize.mul_add, x.toNat_index hs (i := j + 1 + k) (by lia), hjk,
    Nat.mul_add x.inc (j.toNat + 1), Nat.add_assoc]

/-- The `USize` index of element `i < n` is in the array. -/
public theorem toNat_index_lt (x : Vec n) (hs : x.data.size < USize.size) {i : USize}
    (h : i.toNat < n) : (x.off.toUSize + x.inc.toUSize * i).toNat < x.data.size :=
  Stride.toNat_idx_toUSize_lt x.fits hs h

public instance : GetElem (Vec n) Nat Float fun _ i => i < n where
  getElem x i h := x.data[x.off + x.inc * i]'(x.index_lt h)

public theorem getElem_def (x : Vec n) (i : Nat) (h : i < n) :
    x[i] = x.data[x.off + x.inc * i]'(x.index_lt h) := rfl

/--
The element at the `USize` index `i`, in a vector whose array has a `USize` size, as every array
in memory does, given its offset `o` and stride `c` as `USize`s. It compiles to an inline load. A
loop computes `o` and `c` once, before it starts, rather than at each step.
-/
@[inline] public def uget (x : Vec n) (o c : USize) (ho : x.off.toUSize = o)
    (hc : x.inc.toUSize = c) (hs : x.data.size < USize.size) (i : USize) (h : i.toNat < n) :
    Float :=
  x.data.uget (o + c * i) (by rw [← ho, ← hc]; exact x.toNat_index_lt hs h)

@[simp] public theorem uget_eq_getElem (x : Vec n) (o c : USize) (ho : x.off.toUSize = o)
    (hc : x.inc.toUSize = c) (hs : x.data.size < USize.size) (i : USize) (h : i.toNat < n) :
    x.uget o c ho hc hs i h = x[i.toNat] := by
  subst ho hc
  simp only [uget, Float64Array.uget_eq_getElem, getElem_def, x.toNat_index hs h]

/-- The contiguous vector of the elements of `a`, from the index `0`. -/
@[expose] public def ofArray (a : Float64Array) (h : a.size = n) : Vec n where
  data := a
  off := 0
  inc := 1
  inc_pos := Or.inl (by decide)
  bound := by
    rcases Nat.eq_zero_or_pos n with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by lia)

@[simp] public theorem data_ofArray (a : Float64Array) (h : a.size = n) : (ofArray a h).data = a :=
  rfl

@[simp] public theorem getElem_ofArray (a : Float64Array) (h : a.size = n) (i : Nat) (hi : i < n) :
    (ofArray a h)[i] = a[i]'(by lia) := by
  simp [getElem_def, ofArray]

/--
The vector of `n` elements of `a` from the index `off` with the stride `inc`, if they are in `a`
and the stride is positive or `n ≤ 1`.
-/
public def ofStride? (a : Float64Array) (off inc : Nat) : Option (Vec n) :=
  if h : (Stride.mk off inc).Fits n a.size then some ⟨a, off, inc, h.inc_pos, h.idx_last_lt⟩
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
