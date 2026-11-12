/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# Packed matrices

`PMat m n` is an `m × n` matrix of floats, packed in column-major order in a `Float64Array` of
exactly `m * n` elements: the element in row `i` and column `j` is at the index `i + m * j`. The
`gemm` kernels run on packed matrices; `Mat m n` is the general matrix, with an offset and a
leading dimension, which they pack when it isn't packed already.
-/

open ScalarArray

namespace BLAS.Float64

/-- An `m × n` matrix of floats, packed in column-major order in a `Float64Array`. -/
public structure PMat (m n : Nat) where
  /-- The elements, column after column. -/
  data : Float64Array
  /-- The array has `m * n` elements. -/
  size_data : data.size = m * n

/-- The index `i + m * j` of an element of an `m × n` matrix is below `m * n`. -/
public theorem PMat.index_lt {m n i j : Nat} (hi : i < m) (hj : j < n) : i + m * j < m * n := by
  have : m * (j + 1) ≤ m * n := Nat.mul_le_mul_left m hj
  rw [Nat.mul_succ] at this
  lia

namespace PMat

variable {m n : Nat}

/-- `A[(i, j)]` is the element in row `i` and column `j`. -/
public instance : GetElem (PMat m n) (Nat × Nat) Float fun _ p => p.1 < m ∧ p.2 < n where
  getElem A p h := A.data[p.1 + m * p.2]'(by rw [A.size_data]; exact index_lt h.1 h.2)

public theorem getElem_def (A : PMat m n) (i j : Nat) (h : i < m ∧ j < n) :
    A[(i, j)] = A.data[i + m * j]'(by rw [A.size_data]; exact index_lt h.1 h.2) := rfl

/-- The matrix with the elements `f i j`. -/
public def ofFn (f : Fin m → Fin n → Float) : PMat m n :=
  ⟨.ofFn (n := m * n) fun p =>
    have : 0 < m := Nat.pos_of_ne_zero fun h => by have := p.isLt; simp [h] at this
    f ⟨p.val % m, Nat.mod_lt _ this⟩ ⟨p.val / m, Nat.div_lt_of_lt_mul p.isLt⟩, by simp⟩

@[simp] public theorem getElem_ofFn (f : Fin m → Fin n → Float) (i j : Nat)
    (h : i < m ∧ j < n) : (ofFn f)[(i, j)] = f ⟨i, h.1⟩ ⟨j, h.2⟩ := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) h.1
  simp only [getElem_def, ofFn, Float64Array.getElem_ofFn]
  congr
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.1]
  · rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt h.1, Nat.zero_add]

/-- Two matrices with the same elements are equal. -/
public theorem ext {A B : PMat m n} (h : ∀ i j (hij : i < m ∧ j < n), A[(i, j)] = B[(i, j)]) :
    A = B := by
  obtain ⟨a, ha⟩ := A
  obtain ⟨b, hb⟩ := B
  congr
  apply Float64Array.ext_getElem (by rw [ha, hb])
  intro p hpa hpb
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at ha; lia
  have hp : p < m * n := ha ▸ hpa
  have := h (p % m) (p / m) ⟨Nat.mod_lt _ hm, Nat.div_lt_of_lt_mul hp⟩
  simp only [getElem_def] at this
  simpa [Nat.mod_add_div] using this

/-- The elements, column after column. -/
public def toList (A : PMat m n) : List Float := A.data.toList

end PMat

end BLAS.Float64
