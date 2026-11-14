/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.PMat
public import BLAS.Float64.Loop
public import ScalarArray.Notation
import all BLAS.Internal

/-!
# Level 3

The matrix product `gemm`.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

/-- The elements of column `j` of an `m × n` matrix are in the window `m * j ≤ q < m * j + m`. -/
private theorem col_window {m j' i j : Nat} (hi : i < m) :
    (m * j' ≤ i + m * j ∧ i + m * j < m * j' + m) ↔ j' = j := by
  constructor
  · intro ⟨h₁, h₂⟩
    rcases Nat.lt_trichotomy j' j with h | h | h
    · have : m * (j' + 1) ≤ m * j := Nat.mul_le_mul_left m h
      rw [Nat.mul_succ] at this; lia
    · exact h
    · have : m * (j + 1) ≤ m * j' := Nat.mul_le_mul_left m h
      rw [Nat.mul_succ] at this; lia
  · rintro rfl; lia

namespace PMat

variable {m n k : Nat}

/--
The value of `gemm α A B β C` at `(i, j)`: `betaMul β C[i, j]`, plus the terms
`α * B[l, j] * A[i, l]` for `l = 0, …, k - 1`, added from the left, in the order of the reference
BLAS.
-/
@[expose] public def gemmEntry (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (i j : Nat) (hi : i < m) (hj : j < n) : Float :=
  Nat.fold k (fun l hl s => s + α * B[(l, j)] * A[(i, l)]) (betaMul β C[(i, j)])

/-- The model of `gemm`, with `gemmEntry` at each element. -/
public def gemmModel (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n) :
    PMat m n :=
  ofFn fun i j => gemmEntry α A B β C i j i.isLt j.isLt

/--
`gemm α A B β C` is `α * A * B + β * C`, by the naive loops of the reference BLAS: for each column
`j`, it scales the column of `C` by `β`, or sets it to `0` without reading it when `β = 0`, then
adds `α * B[l, j]` times column `l` of `A`, for `l = 0, …, k - 1`. It updates `C` in place when
`C` is not shared. `Mat.gemm` handles the case `α = 0`, which doesn't run this kernel.
-/
public def gemm (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n) : PMat m n :=
  if hs : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m < USize.size ∧ n < USize.size ∧ k < USize.size then
    let mu := m.toUSize
    let nu := n.toUSize
    let ku := k.toUSize
    have hmu : mu.toNat = m := by grind
    have hnu : nu.toNat = n := by grind
    have hku : ku.toNat = k := by grind
    let a := A.data
    let b := B.data
    have ha : a.size = m * k := A.size_data
    have hb : b.size = k * n := B.size_data
    let c := C.data
    have hc : c.size = m * n := C.size_data
    inplace c do
      for j in 0...nu do
        let cj := mu * j
        have hcj : cj.toNat + mu.toNat ≤ c.size :=
          toNat_mul_add_le (n := n) (by lia) (by rw [hmu, hc]; exact Nat.le_refl _)
        for i in 0...mu do
          c[cj + i] := betaMul β c[cj + i]
        for l in 0...ku do
          let al := mu * l
          have hal : al.toNat + mu.toNat ≤ a.size :=
            toNat_mul_add_le (n := k) (by lia) (by rw [hmu, ha]; exact Nat.le_refl _)
          let bj := ku * j
          have hbj : bj.toNat + ku.toNat ≤ b.size :=
            toNat_mul_add_le (n := n) (by lia) (by rw [hku, hb]; exact Nat.le_refl _)
          let t := α * b.uget (bj + l) (Notation.toNat_add_lt_of_window hbj (by lia))
          for i in 0...mu do
            c[cj + i] := c[cj + i] +
              t * a.uget (al + i) (Notation.toNat_add_lt_of_window hal (by lia))
    then fun _ c' h => ⟨c', by rw [h, hc]⟩
  else gemmModel α A B β C

/-! ## The specification of `gemm` -/

/--
The model of the steps of `gemm` for column `j`, on the arrays `a`, `b` and `c` of `A`, `B` and
`C`: it scales the column of `c` by `β`, then adds `α * b[l + k * j] * a[i + m * l]` to the
element `i` of the column, for `l < k`.
-/
private def gemmCol (m k : Nat) (α : Float) (a b : Float64Array) (β : Float) (j : Nat)
    (c : Float64Array) : Float64Array :=
  iterRange (fun l c => iterRange (fun i c =>
      c.set! (m * j + i) (c[m * j + i]! + α * b[k * j + l]! * a[m * l + i]!)) 0 m c) 0 k
    (iterRange (fun i c => c.set! (m * j + i) (betaMul β c[m * j + i]!)) 0 m c)

private theorem size_gemmCol (m k α a b β j) (c : Float64Array) :
    (gemmCol m k α a b β j c).size = c.size := by
  simp [gemmCol, size_iterRange]

private theorem getElem!_gemmCol_of_ne (α a b β) {i j j' : Nat} (hi : i < m) (hj : j' ≠ j)
    (c : Float64Array) (hq : i + m * j < c.size) :
    (gemmCol m k α a b β j' c)[i + m * j]! = c[i + m * j]! := by
  have hw : ¬(m * j' + 0 ≤ i + m * j ∧ i + m * j < m * j' + m) := by
    rw [Nat.add_zero, col_window hi]; exact hj
  unfold gemmCol
  rw [getElem!_iterRange_of_frame]
  · rw [getElem!_iterRange_set! (m * j') (fun _ v => betaMul β v) _ _ _ _ hq, ite_eq_right hw]
  · intro l _ _ c'
    by_cases hc : i + m * j < c'.size
    · rw [getElem!_iterRange_set! (m * j') (fun i v => v + α * b[k * j' + l]! * a[m * l + i]!)
        _ _ _ _ hc, ite_eq_right hw]
    · rw [getElem!_neg c' _ hc, getElem!_neg _ _ (by simpa [size_iterRange] using hc)]

private theorem getElem!_gemmCol (α a b β) {i j : Nat} (hi : i < m) (c : Float64Array)
    (hq : i + m * j < c.size) :
    (gemmCol m k α a b β j c)[i + m * j]! =
      Nat.fold k (fun l _ s => s + α * b[k * j + l]! * a[m * l + i]!) (betaMul β c[i + m * j]!) := by
  have hw : m * j + 0 ≤ i + m * j ∧ i + m * j < m * j + m := by lia
  have hsub : i + m * j - m * j = i := by lia
  unfold gemmCol
  rw [getElem!_iterRange_of_pointwise _ _ _ c.size
      (fun l _ s => s + α * b[k * j + l]! * a[m * l + i]!) (fun _ _ => by simp [size_iterRange])]
  · rw [getElem!_iterRange_set! (m * j) (fun _ v => betaMul β v) _ _ _ _ hq, ite_eq_left hw]
  · intro l _ c' hc
    rw [getElem!_iterRange_set! (m * j) (fun i v => v + α * b[k * j + l]! * a[m * l + i]!)
      _ _ _ _ (by lia), ite_eq_left hw, hsub]
  · simp [size_iterRange]

public theorem gemm_eq (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n) :
    gemm α A B β C = gemmModel α A B β C := by
  unfold gemm
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    have hku : k.toUSize.toNat = k := by grind
    have hA := A.size_data
    have hB := B.size_data
    have hC := C.size_data
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := gemmCol m k α A.data B.data β) (hF := size_gemmCol m k α A.data B.data β)]
    · have hcol := size_gemmCol m k α A.data B.data β
      simp only [Tail.run_done]
      apply ext
      intro i j hij
      have e : ∀ (x : Float64Array) (q : Nat) (h : q < x.size), x[q] = x[q]! :=
        fun x q h => (getElem!_pos x q h).symm
      simp only [gemmModel, getElem_ofFn, gemmEntry]
      simp only [getElem_def, e, hnu, USize.toNat_zero]
      have hq := index_lt hij.1 hij.2
      rw [iterRange_split _ (Nat.zero_le _) (show j + 1 ≤ n by lia), getElem!_iterRange_of_frame,
        iterRange_succ _ (Nat.zero_le _), getElem!_gemmCol _ _ _ _ hij.1 _
          (by rw [size_iterRange _ hcol]; lia),
        getElem!_iterRange_of_frame]
      · congr
        funext l hl s
        rw [Nat.add_comm (k * j), Nat.add_comm (m * l)]
      · intro j' _ hj' c
        by_cases hc : i + m * j < c.size
        · exact getElem!_gemmCol_of_ne _ _ _ _ hij.1 (by lia) c hc
        · rw [getElem!_neg c _ hc, getElem!_neg _ _ (by rw [size_gemmCol]; exact hc)]
      · intro j' hj' _ c
        by_cases hc : i + m * j < c.size
        · exact getElem!_gemmCol_of_ne _ _ _ _ hij.1 (by lia) c hc
        · rw [getElem!_neg c _ hc, getElem!_neg _ _ (by rw [size_gemmCol]; exact hc)]
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_unit (F := fun i c => c.set! (m * j.toNat + i) (betaMul β c[m * j.toNat + i]!))
          (hF := by simp)]
      · rw [Tail.run_forInFrom_unit (F := fun l c => iterRange (fun i c =>
            c.set! (m * j.toNat + i)
              (c[m * j.toNat + i]! + α * B.data[k * j.toNat + l]! * A.data[m * l + i]!)) 0 m c)
            (hF := by simp [size_iterRange])]
        · congr 1
          simp [gemmCol, hmu, hku]
        · intro l _ hl next' a' h'
          rw [hku] at hl
          rw [Tail.run_forInFrom_unit (F := fun i c => c.set! (m * j.toNat + i)
              (c[m * j.toNat + i]! + α * B.data[k * j.toNat + l.toNat]! * A.data[m * l.toNat + i]!))
              (hF := by simp)]
          · simp [hmu]
          · intro i _ hi next'' a'' h''
            rw [hmu] at hi
            simp only [Tail.run_readThen, Tail.run_writeThen]
            apply run_set_eq_set!
            · exact toNat_mul_add_eq hmu hj (Nat.le_of_lt hi) hs.1
            · have h1 := toNat_mul_add_eq hmu hj (Nat.le_of_lt hi) hs.1
              have h2 := toNat_mul_add_eq hku hj (Nat.le_of_lt hl) hs.2.2.1
              have h3 := toNat_mul_add_eq hmu hl (Nat.le_of_lt hi) hs.2.1
              have := index_lt hi hj
              have := index_lt hi hl
              have := index_lt hl hj
              simp only [Float64Array.uget_eq_getElem, h1, h2, h3]
              rw [getElem!_pos a'' _ (by lia), getElem!_pos B.data _ (by lia),
                getElem!_pos A.data _ (by lia)]
      · intro i _ hi next' a' h'
        rw [hmu] at hi
        simp only [Tail.run_readThen, Tail.run_writeThen]
        apply run_set_eq_set!
        · exact toNat_mul_add_eq hmu hj (Nat.le_of_lt hi) hs.1
        · have h1 := toNat_mul_add_eq hmu hj (Nat.le_of_lt hi) hs.1
          have := index_lt hi hj
          simp only [h1]
          rw [getElem!_pos a' _ (by lia)]
  · rfl

@[simp] public theorem getElem_gemm (α : Float) (A : PMat m k) (B : PMat k n) (β : Float)
    (C : PMat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemm α A B β C)[(i, j)] = gemmEntry α A B β C i j h.1 h.2 := by
  rw [gemm_eq]; simp [gemmModel]

end PMat

end BLAS.Float64
