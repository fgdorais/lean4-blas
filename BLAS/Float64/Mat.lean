/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.PMat
public import BLAS.Float64.Vec
public import BLAS.Float64.Loop

/-!
# Matrices

`Mat m n` is an `m × n` matrix of floats, stored in column-major order in a `Float64Array` with an
offset `off` and a leading dimension `ld ≥ m`, as in the reference BLAS: the element in row `i` and
column `j` is at the index `off + ld * j + i`. Its shape is part of its type. Each column is a
contiguous window of the array, and the other elements of the array are not part of the matrix, so
a matrix can be a block of a larger one, and the routines that update a matrix leave them
unchanged.
-/

open ScalarArray Float64Array

namespace BLAS.Float64

/--
An `m × n` matrix of floats, stored in column-major order in a `Float64Array`, from the index
`off`, with the leading dimension `ld`: column `j` starts at `off + ld * j`.
-/
public structure Mat (m n : Nat) where
  /-- The array that holds the elements. -/
  data : Float64Array
  /-- The index of the first element. -/
  off : Nat
  /-- The leading dimension: the distance between the starts of two consecutive columns. -/
  ld : Nat
  /-- The columns don't overlap. -/
  le_ld : m ≤ ld
  /-- The last column is in the array. -/
  bound : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ data.size

namespace Mat

variable {m n : Nat}

/-- Column `j < n` of a matrix with rows is in the array. -/
public theorem col_le (A : Mat m n) {j : Nat} (hm : 0 < m) (hj : j < n) :
    A.off + A.ld * j + m ≤ A.data.size := by
  have : A.ld * j ≤ A.ld * (n - 1) := Nat.mul_le_mul_left _ (by omega)
  rcases A.bound with h | h | h <;> omega

/-- The index `off + ld * j + i` of an element is in the array. -/
public theorem index_lt (A : Mat m n) {i j : Nat} (hi : i < m) (hj : j < n) :
    A.off + A.ld * j + i < A.data.size := by
  have := A.col_le (by omega) hj; omega

/--
The `USize` index `off + ld * j + i` of an element, in an array of `USize` size, doesn't wrap
around.
-/
public theorem toNat_index (A : Mat m n) (hs : A.data.size < USize.size) {i j : USize}
    (hi : i.toNat < m) (hj : j.toNat < n) :
    (A.off.toUSize + A.ld.toUSize * j + i).toNat = A.off + A.ld * j.toNat + i.toNat := by
  have h₁ := A.index_lt hi hj
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have ho : A.off.toUSize.toNat = A.off := by
    simp [Nat.mod_eq_of_lt (show A.off < USize.size by omega)]
  have hm : (A.ld.toUSize * j).toNat = A.ld * j.toNat := by
    rcases Nat.eq_zero_or_pos j.toNat with h₀ | h₀
    · have : j = 0 := USize.toNat_inj.mp (by simpa using h₀)
      subst this
      simp
    · have hl : A.ld ≤ A.ld * j.toNat := Nat.le_mul_of_pos_right _ h₀
      have hc : A.ld.toUSize.toNat = A.ld := by
        simp [Nat.mod_eq_of_lt (show A.ld < USize.size by omega)]
      rw [USize.toNat_mul, hc, Nat.mod_eq_of_lt (by omega)]
  rw [USize.toNat_add, USize.toNat_add, ho, hm, Nat.mod_eq_of_lt (a := A.off + A.ld * j.toNat)
    (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The `USize` index of an element, as the step `i` of column `j` with the stride `1`. -/
public theorem toNat_col_index (A : Mat m n) (hs : A.data.size < USize.size) {i j : USize}
    (hi : i.toNat < m) (hj : j.toNat < n) :
    (A.off.toUSize + A.ld.toUSize * j + 1 * i).toNat = A.off + A.ld * j.toNat + 1 * i.toNat := by
  rw [USize.one_mul, Nat.one_mul, A.toNat_index hs hi hj]

/-- The `USize` index of an element, as the step `i` of column `j`, is in the array. -/
public theorem toNat_col_index_lt (A : Mat m n) (hs : A.data.size < USize.size) {i j : USize}
    (hi : i.toNat < m) (hj : j.toNat < n) :
    (A.off.toUSize + A.ld.toUSize * j + 1 * i).toNat < A.data.size := by
  rw [A.toNat_col_index hs hi hj, Nat.one_mul]; exact A.index_lt hi hj

/--
The element at the `USize` indices `i` and `j`, in a matrix whose array has a `USize` size, given
its offset `o` and leading dimension `l` as `USize`s, computed once before a loop. It compiles to
an inline load.
-/
@[inline] public def uget (A : Mat m n) (o l : USize) (ho : A.off.toUSize = o)
    (hl : A.ld.toUSize = l) (hs : A.data.size < USize.size) (i j : USize) (hi : i.toNat < m)
    (hj : j.toNat < n) : Float :=
  A.data.uget (o + l * j + i) (by rw [← ho, ← hl, A.toNat_index hs hi hj]; exact A.index_lt hi hj)

/-- `A[(i, j)]` is the element in row `i` and column `j`. -/
public instance : GetElem (Mat m n) (Nat × Nat) Float fun _ p => p.1 < m ∧ p.2 < n where
  getElem A p h := A.data[A.off + A.ld * p.2 + p.1]'(A.index_lt h.1 h.2)

public theorem getElem_def (A : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    A[(i, j)] = A.data[A.off + A.ld * j + i]'(A.index_lt h.1 h.2) := rfl

@[simp] public theorem uget_eq_getElem (A : Mat m n) (o l : USize) (ho : A.off.toUSize = o)
    (hl : A.ld.toUSize = l) (hs : A.data.size < USize.size) (i j : USize) (hi : i.toNat < m)
    (hj : j.toNat < n) : A.uget o l ho hl hs i j hi hj = A[(i.toNat, j.toNat)] := by
  subst ho hl
  simp only [uget, Float64Array.uget_eq_getElem, getElem_def, A.toNat_index hs hi hj]

/-- The matrix of a packed matrix, with no copy. -/
@[expose] public def ofPMat (A : PMat m n) : Mat m n where
  data := A.data
  off := 0
  ld := m
  le_ld := Nat.le_refl _
  bound := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ?_)
      rw [A.size_data, Nat.zero_add, ← Nat.mul_succ]
      exact Nat.le_of_eq (by congr 1; omega)

@[simp] public theorem getElem_ofPMat (A : PMat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (ofPMat A)[(i, j)] = A[(i, j)] := by
  simp only [getElem_def, ofPMat, PMat.getElem_def]
  congr 1
  omega

/-- The packed matrix with the elements `f i j`. -/
public def ofFn (f : Fin m → Fin n → Float) : Mat m n := ofPMat (.ofFn f)

@[simp] public theorem getElem_ofFn (f : Fin m → Fin n → Float) (i j : Nat)
    (h : i < m ∧ j < n) : (ofFn f)[(i, j)] = f ⟨i, h.1⟩ ⟨j, h.2⟩ := by
  simp [ofFn]

/--
The matrix of the `m × n` elements of `a` from the index `off` with the leading dimension `ld`, if
they are in `a` and `m ≤ ld`.
-/
public def ofLd? (a : Float64Array) (off ld : Nat) : Option (Mat m n) :=
  if h : m ≤ ld ∧ (m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ a.size) then
    some ⟨a, off, ld, h.1, h.2⟩
  else none

/-- The elements, column after column. -/
public def toList (A : Mat m n) : List Float :=
  (List.ofFn fun j : Fin n => List.ofFn fun i : Fin m => A[(i.val, j.val)]).flatten

/-- Column `j` as a vector, with no copy. -/
public def col (A : Mat m n) (j : Nat) (hj : j < n) : Vec m where
  data := A.data
  off := A.off + A.ld * j
  inc := 1
  inc_pos := Or.inl Nat.one_pos
  bound := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inl h
    · exact Or.inr (by have := A.col_le h hj; omega)

@[simp] public theorem getElem_col (A : Mat m n) (j : Nat) (hj : j < n) (i : Nat) (hi : i < m) :
    (A.col j hj)[i] = A[(i, j)] := by
  simp only [Vec.getElem_def, getElem_def, col, Nat.one_mul]

/-- Row `i` as a vector, with no copy. -/
public def row (A : Mat m n) (i : Nat) (hi : i < m) : Vec n where
  data := A.data
  off := A.off + i
  inc := A.ld
  inc_pos := by
    rcases Nat.lt_or_ge n 2 with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by have := A.le_ld; omega)
  bound := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · exact Or.inr (by have := A.index_lt hi (j := n - 1) (by omega); omega)

@[simp] public theorem getElem_row (A : Mat m n) (i : Nat) (hi : i < m) (j : Nat) (hj : j < n) :
    (A.row i hi)[j] = A[(i, j)] := by
  simp only [Vec.getElem_def, getElem_def, row]
  congr 1
  omega

end Mat

/-! ## The model of a matrix update -/

/--
The array `a` with `g i j a[off + ld * j + i]` at the indices `off + ld * j + i` of the elements
of an `m × n'` matrix, for `i < m` and `lo ≤ j < hi`.
-/
public def mapMat (a : Float64Array) (off ld m lo hi : Nat) (g : Nat → Nat → Float → Float) :
    Float64Array :=
  .ofFn (n := a.size) fun p =>
    if off ≤ p.val ∧ (p.val - off) % ld < m ∧ lo ≤ (p.val - off) / ld ∧ (p.val - off) / ld < hi
    then g ((p.val - off) % ld) ((p.val - off) / ld) a[p.val] else a[p.val]

@[simp] public theorem size_mapMat (a : Float64Array) (off ld m lo hi g) :
    (mapMat a off ld m lo hi g).size = a.size := by
  simp [mapMat]

/-- The index `off + ld * j + i` is row `i` and column `j`, for `i < ld`. -/
theorem mat_index {off ld i j : Nat} (h : i < ld) :
    (off + ld * j + i - off) % ld = i ∧ (off + ld * j + i - off) / ld = j := by
  have e : off + ld * j + i - off = i + ld * j := by omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt h, Nat.zero_add]
  exact ⟨rfl, rfl⟩

/-- An index `p ≥ off` is `off + ld * ((p - off) / ld) + (p - off) % ld`. -/
theorem eq_mat_index {off ld p : Nat} (h : off ≤ p) :
    p = off + ld * ((p - off) / ld) + (p - off) % ld := by
  have := Nat.div_add_mod (p - off) ld
  omega

/-- The element in row `i` and column `j`. -/
public theorem getElem_mapMat_index (a : Float64Array) (off ld m lo hi g) {i j : Nat}
    (hr : i < m) (hml : m ≤ ld) (hj : lo ≤ j ∧ j < hi) (h : off + ld * j + i < a.size) :
    (mapMat a off ld m lo hi g)[off + ld * j + i]'(by simpa using h) =
      g i j a[off + ld * j + i] := by
  obtain ⟨h₁, h₂⟩ := mat_index (off := off) (j := j) (show i < ld by omega)
  simp only [mapMat, getElem_ofFn]
  rw [ite_eq_left (by rw [h₁, h₂]; exact ⟨by omega, hr, hj⟩), h₁, h₂]

/-- An element at no index of the matrix is unchanged. -/
public theorem getElem_mapMat_of_ne (a : Float64Array) (off ld m lo hi g) {p : Nat}
    (hp : ∀ i j, i < m → lo ≤ j → j < hi → p ≠ off + ld * j + i) (h : p < a.size) :
    (mapMat a off ld m lo hi g)[p]'(by simpa using h) = a[p] := by
  simp only [mapMat, getElem_ofFn]
  rw [ite_eq_right]
  intro ⟨h₁, h₂, h₃, h₄⟩
  exact hp _ _ h₂ h₃ h₄ (eq_mat_index h₁)

public theorem mapMat_of_le (a : Float64Array) (off ld m lo hi g) (h : hi ≤ lo) :
    mapMat a off ld m lo hi g = a := by
  apply ext_getElem (by simp)
  intro p _ hp
  exact getElem_mapMat_of_ne a off ld m lo hi g (fun i j _ h₁ h₂ => by omega) hp

namespace Mat

variable {m n : Nat}

/-- `mapMat` depends only on the values of its function in the matrix. -/
public theorem _root_.BLAS.Float64.mapMat_congr (a : Float64Array) (off ld m lo hi : Nat) {g g' : Nat → Nat → Float → Float}
    (h : ∀ i j v, i < m → lo ≤ j → j < hi → g i j v = g' i j v) :
    mapMat a off ld m lo hi g = mapMat a off ld m lo hi g' := by
  apply ext_getElem (by simp)
  intro p _ _
  simp only [mapMat, Float64Array.getElem_ofFn]
  split
  · rename_i hc; exact h _ _ _ hc.2.1 hc.2.2.1 hc.2.2.2
  · rfl

/--
A matrix `B` whose array is the array of `A` with the element `(i, j)` mapped by `g i j`, at the
same indices, has the elements `g i j A[(i, j)]`.
-/
public theorem getElem_of_data_eq_mapMat {A B : Mat m n} (g : Nat → Nat → Float → Float)
    (hd : B.data = mapMat A.data A.off A.ld m 0 n g) (ho : B.off = A.off) (hl : B.ld = A.ld)
    (i j : Nat) (h : i < m ∧ j < n) : B[(i, j)] = g i j A[(i, j)] := by
  simp only [getElem_def]
  have hq := A.index_lt h.1 h.2
  have e : B.data[B.off + B.ld * j + i]'(B.index_lt h.1 h.2) =
      (mapMat A.data A.off A.ld m 0 n g)[A.off + A.ld * j + i]'(by simpa using hq) := by
    simp only [hd, ho, hl]
  rw [e, getElem_mapMat_index _ _ _ _ _ _ _ h.1 A.le_ld ⟨Nat.zero_le _, h.2⟩ hq]

/-- Mapping column `n` of a matrix, as a stride of `1`, adds it to the columns before it. -/
theorem mapStride_mapMat (a : Float64Array) (off ld : Nat) (hml : m ≤ ld) (j : Nat)
    (g : Nat → Nat → Float → Float) :
    mapStride (mapMat a off ld m 0 j g) (off + ld * j) 1 0 m (fun i v => g i j v) =
      mapMat a off ld m 0 (j + 1) g := by
  apply ext_getElem (by simp)
  intro p h₁ h₂
  simp only [size_mapMat] at h₂
  by_cases hw : ∃ i, i < m ∧ p = off + ld * j + i
  · obtain ⟨i, hi, rfl⟩ := hw
    have e : ∀ (b : Float64Array) (h : off + ld * j + i < b.size),
        b[off + ld * j + i] = b[off + ld * j + 1 * i]'(by rw [Nat.one_mul]; exact h) := by
      intro b h; simp only [Nat.one_mul]
    rw [e _ h₁, getElem_mapStride_stride _ _ _ _ _ _ ⟨Nat.zero_le _, hi⟩ (Or.inl Nat.one_pos)
      (by simpa using h₂), getElem_mapMat_index _ _ _ _ _ _ _ hi hml ⟨Nat.zero_le _, by omega⟩ h₂]
    simp only [Nat.one_mul]
    rw [getElem_mapMat_of_ne _ _ _ _ _ _ _ ?_ (by simpa using h₂)]
    intro i' j' hi' _ hj' he
    have h₁ := mat_index (off := off) (j := j) (show i < ld by omega)
    have h₂ := mat_index (off := off) (j := j') (show i' < ld by omega)
    rw [he] at h₁
    omega
  · have hne : ∀ i, 0 ≤ i → i < m → p ≠ off + ld * j + 1 * i :=
      fun i _ hi e => hw ⟨i, hi, by omega⟩
    rw [getElem_mapStride_of_ne _ _ _ _ _ _ hne (by simpa using h₂)]
    simp only [mapMat, Float64Array.getElem_ofFn]
    by_cases hc : off ≤ p ∧ (p - off) % ld < m
    · have e := eq_mat_index (ld := ld) hc.1
      have hj' : (p - off) / ld ≠ j := fun h' => hw ⟨_, hc.2, by rw [← h']; exact e⟩
      by_cases hr : (p - off) / ld < j + 1
      · rw [ite_eq_left ⟨hc.1, hc.2, Nat.zero_le _, by omega⟩,
          ite_eq_left ⟨hc.1, hc.2, Nat.zero_le _, hr⟩]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Steps that each map column `j` of a matrix, as a stride of `1`, map the whole matrix. -/
public theorem iterRange_cols (a : Float64Array) (off ld : Nat) (hml : m ≤ ld) (n : Nat)
    (G : Nat → Nat → Float → Float) :
    iterRange (fun j c => mapStride c (off + ld * j) 1 0 m (G j)) 0 n a =
      mapMat a off ld m 0 n fun i j v => G j i v := by
  induction n with
  | zero => rw [iterRange_of_le _ (Nat.le_refl _), mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ n ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih]
    exact mapStride_mapMat a off ld hml n _

/-! ## Packing -/

/-- Whether a matrix is packed: from the index `0`, with `ld = m`, in an array of `m * n`. -/
@[expose] public def IsPacked (A : Mat m n) : Prop := A.off = 0 ∧ A.ld = m ∧ A.data.size = m * n

public instance (A : Mat m n) : Decidable A.IsPacked := by unfold IsPacked; infer_instance

/-- Copies the columns `j` and up of `A` into the packed array `c`. -/
public def packCols (A : Mat m n) (j : Nat) (c : Float64Array) : Float64Array :=
  if j < n then packCols A (j + 1) (A.data.copySlice (A.off + A.ld * j) c (m * j) m) else c
termination_by n - j

/-- Column `j < n` of a packed `m × n` array is in it. -/
theorem packed_col_le {j : Nat} (hj : j < n) : m * j + m ≤ m * n := by
  have : m * (j + 1) ≤ m * n := Nat.mul_le_mul_left _ hj
  rwa [Nat.mul_succ] at this

theorem size_packCols (A : Mat m n) (j : Nat) (c : Float64Array) (hc : c.size = m * n) :
    (packCols A j c).size = m * n := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing j c with
  | zero => rw [packCols, ite_eq_right (by omega)]; exact hc
  | succ d ih =>
    rw [packCols, ite_eq_left (by omega)]
    apply ih _ _ _ (by omega)
    have := packed_col_le (m := m) (show j < n by omega)
    rw [size_copySlice, hc]
    omega

theorem getElem!_packCols (A : Mat m n) (j : Nat) (c : Float64Array) (hc : c.size = m * n)
    (hinv : ∀ i j', (h : i < m ∧ j' < n) → j' < j → c[i + m * j']! = A[(i, j')]) :
    ∀ i j', (h : i < m ∧ j' < n) → (packCols A j c)[i + m * j']! = A[(i, j')] := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing j c with
  | zero =>
    rw [packCols, ite_eq_right (by omega)]
    exact fun i j' h => hinv i j' h (by omega)
  | succ d ih =>
    rw [packCols, ite_eq_left (by omega)]
    have hcol := packed_col_le (m := m) (show j < n by omega)
    have hsz : (A.data.copySlice (A.off + A.ld * j) c (m * j) m).size = m * n := by
      rw [size_copySlice, hc]; omega
    refine ih (j + 1) _ hsz ?_ (by omega)
    intro i j' h hj'
    have hq := PMat.index_lt (m := m) h.1 h.2
    have hle : m * j' ≤ m * j := Nat.mul_le_mul_left _ (show j' ≤ j by omega)
    rw [getElem!_pos _ _ (by rw [hsz]; exact hq), getElem_copySlice]
    by_cases hlt : j' < j
    · have : i + m * j' < m * j := by
        have : m * (j' + 1) ≤ m * j := Nat.mul_le_mul_left _ hlt
        rw [Nat.mul_succ] at this; omega
      rw [dite_eq_left (by omega), ← getElem!_pos c _ (by omega), hinv i j' h hlt]
    · obtain rfl : j' = j := by omega
      have := A.index_lt h.1 h.2
      rw [dite_eq_right (by omega), dite_eq_left (by omega), getElem_def]
      congr 1
      omega

/--
The packed matrix with the elements of `A`: its array when `A` is packed, and otherwise a copy of
its columns, one `memmove` each.
-/
public def pack (A : Mat m n) : PMat m n :=
  if h : A.IsPacked then ⟨A.data, h.2.2⟩
  else ⟨packCols A 0 (replicate (m * n) 0), size_packCols A 0 _ (by simp)⟩

@[simp] public theorem getElem_pack (A : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (pack A)[(i, j)] = A[(i, j)] := by
  unfold pack
  split
  · rename_i hp
    simp only [PMat.getElem_def, getElem_def, hp.1, hp.2.1]
    congr 1
    omega
  · simp only [PMat.getElem_def]
    rw [← getElem!_pos, getElem!_packCols A 0 _ (by simp) (fun _ _ _ h => by omega) i j h]

/-- Writes the columns `j` and up of `P` over the columns of the matrix at `off` with `ld`. -/
public def unpackCols (P : PMat m n) (off ld j : Nat) (c : Float64Array) : Float64Array :=
  if j < n then unpackCols P off ld (j + 1) (P.data.copySlice (m * j) c (off + ld * j) m) else c
termination_by n - j

/-- Writing column `j` of `P` adds it to the model of the columns before it. -/
theorem copySlice_mapMat (P : PMat m n) (a : Float64Array) (off ld j : Nat) (hml : m ≤ ld)
    (hj : j < n) (hcol : m = 0 ∨ off + ld * j + m ≤ a.size) :
    P.data.copySlice (m * j) (mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!)
        (off + ld * j) m =
      mapMat a off ld m 0 (j + 1) fun i j _ => P.data[i + m * j]! := by
  have hP := P.size_data
  have hPj : m * j + m ≤ m * n := by
    have : m * (j + 1) ≤ m * n := Nat.mul_le_mul_left _ hj
    rwa [Nat.mul_succ] at this
  have hsz := size_mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!
  apply ext_getElem (by simp only [size_copySlice, hsz, size_mapMat]; omega)
  intro p h₁ h₂
  rw [size_mapMat] at h₂
  rw [getElem_copySlice]
  by_cases hw : off + ld * j ≤ p ∧ p < off + ld * j + m
  · obtain ⟨i, rfl⟩ : ∃ i, p = off + ld * j + i := ⟨p - (off + ld * j), by omega⟩
    rw [dite_eq_right (by omega), dite_eq_left (by omega),
      getElem_mapMat_index _ _ _ _ _ _ _ (by omega) hml ⟨Nat.zero_le _, by omega⟩ h₂,
      ← getElem!_pos P.data _ (by omega)]
    congr 1
    omega
  · have hne : ∀ i, i < m → p ≠ off + ld * j + i := fun i hi e => hw (by omega)
    have e : (if h : p < min (off + ld * j) (mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!).size
        then (mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!)[p]'(by omega)
        else if h₂ : p - min (off + ld * j) (mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!).size <
          min m (P.data.size - m * j) then P.data[m * j + (p - min (off + ld * j)
            (mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!).size)]'(by omega)
        else (mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!)[p]'(by omega)) =
        (mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!)[p]'(by omega) := by
      split
      · rfl
      · rename_i H
        rw [dite_eq_right]
        rw [hsz] at H ⊢
        rw [hP]
        rcases hcol with hcol | hcol
        · subst hcol; simp
        · omega
    rw [e]
    simp only [mapMat, Float64Array.getElem_ofFn]
    by_cases hc : off ≤ p ∧ (p - off) % ld < m
    · have e' := eq_mat_index (ld := ld) hc.1
      have hj' : (p - off) / ld ≠ j := fun h' => hne _ hc.2 (by rw [← h']; exact e')
      by_cases hr : (p - off) / ld < j + 1
      · rw [ite_eq_left ⟨hc.1, hc.2, Nat.zero_le _, by omega⟩,
          ite_eq_left ⟨hc.1, hc.2, Nat.zero_le _, hr⟩]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem unpackCols_eq (P : PMat m n) (a : Float64Array) (off ld j : Nat) (hml : m ≤ ld)
    (hj : j ≤ n) (hcol : ∀ j', j' < n → m = 0 ∨ off + ld * j' + m ≤ a.size) :
    unpackCols P off ld j (mapMat a off ld m 0 j fun i j _ => P.data[i + m * j]!) =
      mapMat a off ld m 0 n fun i j _ => P.data[i + m * j]! := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing j with
  | zero =>
    obtain rfl : j = n := by omega
    rw [unpackCols, ite_eq_right (Nat.lt_irrefl _)]
  | succ d ih =>
    rw [unpackCols, ite_eq_left (by omega), copySlice_mapMat P a off ld j hml (by omega) (hcol j (by omega)),
      ih (j + 1) (by omega) (by omega)]

/--
The array of `C` with the elements of `P` written over the elements of `C`: `P`'s array, with no
copy, when `C` is packed, and a copy of each column into `C`'s array otherwise.
-/
public def unpack (C : Mat m n) (P : PMat m n) : Float64Array :=
  if C.IsPacked then P.data else unpackCols P C.off C.ld 0 C.data

public theorem unpack_of_isPacked (C : Mat m n) (h : C.IsPacked) (P : PMat m n) :
    unpack C P = P.data := by
  simp [unpack, h]

public theorem unpack_eq (C : Mat m n) (P : PMat m n) :
    unpack C P = mapMat C.data C.off C.ld m 0 n fun i j _ => P.data[i + m * j]! := by
  unfold unpack
  split
  · rename_i hp
    obtain ⟨ho, hl, hs⟩ := hp
    have hP := P.size_data
    apply ext_getElem (by simp [hs, hP])
    intro p h₁ h₂
    simp only [mapMat, Float64Array.getElem_ofFn, ho, hl, Nat.zero_le, true_and, Nat.sub_zero]
    have hm : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hP; omega
    rw [ite_eq_left ⟨Nat.mod_lt _ hm, Nat.div_lt_of_lt_mul (by omega)⟩,
      getElem!_pos P.data _ (by rw [Nat.mod_add_div]; exact h₁)]
    congr 1
    exact (Nat.mod_add_div p m).symm
  · have h0 := unpackCols_eq P C.data C.off C.ld 0 C.le_ld (Nat.zero_le _)
      (fun j hj => by
        rcases Nat.eq_zero_or_pos m with h | h
        · exact Or.inl h
        · exact Or.inr (C.col_le h hj))
    rwa [mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)] at h0

end Mat

end BLAS.Float64
