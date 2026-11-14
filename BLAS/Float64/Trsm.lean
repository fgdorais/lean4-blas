/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Trsv
public import BLAS.Float64.Gemm
import all BLAS.Internal

/-!
# Triangular solve with several right-hand sides

`Mat.trsm uplo d α A B` solves `A * X = α * B` and `Mat.trsmRight uplo d α A B` solves
`X * A = α * B`, for a triangular matrix `A`, over `B`, by the loops of the reference BLAS. Each
element gets the operations of those loops, in the same order. As in the reference BLAS, both set
`B` to `0` without reading `A` or `B` when `α = 0`, and neither checks for a zero on the diagonal.

`trsm` solves each column of `B` by the loops of `trsv`, after scaling it by `α`, so its
specification is that of `trsv` on the scaled column. It solves four columns at a time, which
share the reads of `A`: the columns are independent, so each keeps the order of its operations.
`trsmRight` updates column `j` of `B` with the columns already solved, and its specification is
the recursive model `trsmRightUpper` or `trsmRightLower`.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

/--
The number of rows that the last loop of `trsmRight` divides in a column: `0` for a unit diagonal.
It is not inlined, as `Uplo.loU`.
-/
@[noinline, expose] public def Diag.rows : Diag → USize → USize
  | .unit, _ => 0
  | .nonUnit, mu => mu

public theorem Diag.toNat_rows_le (d : Diag) {mu : USize} : (d.rows mu).toNat ≤ mu.toNat := by
  cases d <;> simp [Diag.rows]

namespace Mat

variable {m n : Nat}

/-- Element `l` of a vector, by `getElem!` on its array. -/
private theorem getElem!_index (x : Vec n) {l : Nat} (hl : l < n) :
    x.data[x.off + x.inc * l]! = x[l] := by
  rw [getElem!_pos x.data _ (x.index_lt hl)]; rfl

/-- An element of a column `j` outside the columns of a `mapMat` is unchanged. -/
private theorem getElem!_mapMat_col_of_not (a : Float64Array) (off ld lo hi : Nat)
    (g : Nat → Nat → Float → Float) (hml : m ≤ ld) {j : Nat} (hj : ¬(lo ≤ j ∧ j < hi)) {l : Nat}
    (hl : l < m) : (mapMat a off ld m lo hi g)[off + ld * j + l]! = a[off + ld * j + l]! := by
  by_cases hq : off + ld * j + l < a.size
  · rw [getElem!_pos _ _ (by rw [size_mapMat]; exact hq), getElem!_pos a _ hq,
      getElem_mapMat_of_ne _ _ _ _ _ _ _ (fun i' j' hi' h₁ h₂ e' => by
        by_cases hjj : j = j'
        · subst hjj; exact hj ⟨h₁, h₂⟩
        · exact col_index_ne hl hi' hml hjj e') hq]
  · rw [getElem!_neg _ _ (by rw [size_mapMat]; exact hq), getElem!_neg a _ hq]

/-! ## The solutions of `trsv` depend only on the elements of the vector -/

theorem trsvLower_congr (d : Diag) (A : Mat n n) {x y : Vec n}
    (h : ∀ l, l < n → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) :
    ∀ i, i < n → trsvLower d A x i = trsvLower d A y i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    rw [trsvLower_eq d A x hi, trsvLower_eq d A y hi, Vec.getElem_def, Vec.getElem_def,
      ← getElem!_pos x.data _ (x.index_lt hi), ← getElem!_pos y.data _ (y.index_lt hi), h i hi]
    congr 2
    funext l hl s
    rw [ih l hl (by lia)]

theorem trsvUpper_congr (d : Diag) (A : Mat n n) {x y : Vec n}
    (h : ∀ l, l < n → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) :
    ∀ i, i < n → trsvUpper d A x i = trsvUpper d A y i := by
  intro i hi
  obtain ⟨e, he⟩ : ∃ e, n - i = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing i with
  | ind e ih =>
    rw [trsvUpper_eq d A x hi, trsvUpper_eq d A y hi, Vec.getElem_def, Vec.getElem_def,
      ← getElem!_pos x.data _ (x.index_lt hi), ← getElem!_pos y.data _ (y.index_lt hi), h i hi]
    congr 2
    funext t ht s
    rw [ih (n - (n - 1 - t)) (by lia) (n - 1 - t) (by lia) rfl]

theorem trsvSol_congr (uplo : Uplo) (d : Diag) (A : Mat n n) {x y : Vec n}
    (h : ∀ l, l < n → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) (i : Nat)
    (hi : i < n) : trsvSol uplo d A x i = trsvSol uplo d A y i := by
  cases uplo
  · exact trsvUpper_congr d A h i hi
  · exact trsvLower_congr d A h i hi

/-! ## `trsm` -/

/-- Column `j` of `B`, scaled by `α`, as a vector. -/
@[expose] public def scaledCol (α : Float) (B : Mat m n) (j : Nat) : Vec m :=
  Vec.ofFn fun l => α * B.data[B.off + B.ld * j + l.val]!

/--
The value of `trsm` at `(i, j)`: `0` when `α = 0`, and element `i` of the solution of
`A * y = α * B[:, j]` by `trsv` otherwise.
-/
@[expose] public def trsmAt (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (i j : Nat) : Float :=
  if α == 0 then 0 else trsvSol uplo d A (scaledCol α B j) i

/--
Column `j` of the array `b` of size `sz`, laid out as an `m × n` matrix from the index `off` with
the leading dimension `ld`, as a vector.
-/
@[expose] public def colOf (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz)
    (b : Float64Array) (hb : b.size = sz) (j : Nat) (hj : j < n) : Vec m where
  data := b
  off := off + ld * j
  inc := 1
  inc_pos := Or.inl Nat.one_pos
  bound := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inl h
    · have : ld * j ≤ ld * (n - 1) := Nat.mul_le_mul_left _ (by lia)
      exact Or.inr (by rcases hsz with h' | h' | h' <;> lia)

private theorem size_scalData_colOf (α : Float) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) : (Vec.scalData α (colOf off ld sz hsz b hb j hj)).size = sz := by
  rw [Vec.scalData_eq, size_modifyAt]; exact hb

private theorem size_trsvData_colOf (uplo : Uplo) (d : Diag) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) : (trsvData uplo d A (colOf off ld sz hsz b hb j hj)).size = sz := by
  rw [trsvData_eq, size_modifyAt]; exact hb

/-! ## Four columns at a time -/

/-
The bounds of the column programs below. They are lemmas, not `by` blocks, so that the loops'
bodies have the shape of the loop lemmas.
-/

private theorem col_lt {sz : Nat} {cq j : USize} (hw : cq.toNat + m ≤ sz) (hj : j.toNat < m) :
    (cq + j).toNat < sz :=
  ScalarArray.Notation.toNat_add_lt_of_window_of_lt hw hj

private theorem below_lt {mu j i : USize} (hmu : mu.toNat = m) (hj : j.toNat < m)
    (hi : i.toNat < (mu - j - 1).toNat) : (j + 1 + i).toNat < m := by
  have : (mu - j - 1).toNat = m - j.toNat - 1 := by grind
  have : m < USize.size := by grind
  rw [toNat_succ_add (by lia)]
  lia

private theorem col_below_lt {sz : Nat} {cq mu j i : USize} (hw : cq.toNat + m ≤ sz)
    (hmu : mu.toNat = m) (hj : j.toNat < m) (hi : i.toNat < (mu - j - 1).toNat) :
    (cq + (j + 1 + i)).toNat < sz :=
  col_lt hw (below_lt hmu hj hi)

/-- The column at the index `o` of `s`, with stride `1`, as a vector. -/
def colAt (s : Float64Array) (o : Nat) (h : o + m ≤ s.size) : Vec m where
  data := s
  off := o
  inc := 1
  inc_pos := Or.inl Nat.one_pos
  bound := by
    rcases Nat.eq_zero_or_pos m with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by lia)

/--
The value of the lower solve of `x` after the steps `l < j`, at the element `i` of old value `v`:
solved for `i < j`, and with the terms of the steps `l < j` otherwise.
-/
def lowerAt (d : Diag) (A : Mat m m) (x : Vec m) (j i : Nat) (v : Float) : Float :=
  if i < j then trsvLower d A x i
  else Nat.fold j (fun l _ s => s - trsvLower d A x l * A.data[A.off + A.ld * l + i]!) v

/-- The program that scales the column at `cq` by `α`, followed by `k`. -/
@[inline] def colScaleT {sz : Nat} {γ : Type} (α : Float) (mu : USize) (hmu : mu.toNat = m)
    (cq : USize) (hw : cq.toNat + m ≤ sz) (k : Tail sz γ) : Tail sz γ :=
  Tail.forInFrom 0 mu 0 (Nat.le_refl _) () (fun i _ hi next _ =>
    Tail.readThen (cq + i) (col_lt hw (hmu ▸ hi)) fun v =>
      Tail.writeThen (cq + i) (col_lt hw (hmu ▸ hi)) (α * v) (next ()))
    fun _ => k

theorem run_colScaleT {sz : Nat} {γ : Type} (α : Float) (mu : USize) (hmu : mu.toNat = m)
    (cq : USize) (hw : cq.toNat + m ≤ sz) (hsz : sz < USize.size) (k : Tail sz γ)
    (a : Float64Array) (h : a.size = sz) :
    (colScaleT α mu hmu cq hw k).run a h =
      k.run (a.modifyAt (Stride.mk cq.toNat 1).idx 0 m fun _ v => α * v)
        (by rw [size_modifyAt]; exact h) := by
  unfold colScaleT
  rw [Tail.run_forInFrom_modify (lo := 0) (hi := mu) (j₀ := 0) (e := fun i => cq + i)
    (idx := (Stride.mk cq.toNat 1).idx)
    (he := fun i _ hi => by
      have := col_lt hw (hmu ▸ hi)
      simp only [Stride.idx]
      rw [USize.toNat_add, Nat.mod_eq_of_lt (by lia)]
      lia)
    (G := fun _ v => α * v)]
  · simp only [USize.toNat_zero, hmu]
  · intro _ _ _ _; rfl



/-- Row `r` of the four columns at `o₀` to `o₃`: element `q` less `t q * a`. -/
def rowSub4 (o₀ o₁ o₂ o₃ r : Nat) (t₀ t₁ t₂ t₃ a : Float) (s : Float64Array) : Float64Array :=
  (((s.set! (o₀ + r) (s[o₀ + r]! - t₀ * a)).set! (o₁ + r) (s[o₁ + r]! - t₁ * a)).set!
    (o₂ + r) (s[o₂ + r]! - t₂ * a)).set! (o₃ + r) (s[o₃ + r]! - t₃ * a)

/--
Step `j` of the solve of the four columns at `o₀` to `o₃`, with stride `1`: solve for their
elements `j`, then update their elements `base` to `base + cnt - 1`, a row of the four at a time.
-/
def stepRows4 (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ j base cnt : Nat) (b : Float64Array) :
    Float64Array :=
  let ajj := A.data[A.off + A.ld * j + j]!
  let t₀ := d.apply b[o₀ + j]! ajj
  let t₁ := d.apply b[o₁ + j]! ajj
  let t₂ := d.apply b[o₂ + j]! ajj
  let t₃ := d.apply b[o₃ + j]! ajj
  iterRange (fun i s => rowSub4 o₀ o₁ o₂ o₃ (base + i) t₀ t₁ t₂ t₃
      A.data[A.off + A.ld * j + (base + i)]! s) 0 cnt
    ((((b.set! (o₀ + j) t₀).set! (o₁ + j) t₁).set! (o₂ + j) t₂).set! (o₃ + j) t₃)

theorem size_stepRows4 (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ j base cnt : Nat)
    (b : Float64Array) : (stepRows4 d A o₀ o₁ o₂ o₃ j base cnt b).size = b.size := by
  unfold stepRows4
  rw [size_iterRange _ (fun _ _ => by simp [rowSub4])]
  simp

/--
`stepRows4` maps four columns of a `mapMat` of `L` to the `mapMat` of `L'`, when `L'` solves for
the elements `j` of `L` and subtracts their terms from the elements `base` to `base + cnt - 1`, and
leaves the others.
-/
theorem stepRows4_mapMat (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat) (hml : m ≤ ld)
    (c : Nat) (hq : off + ld * (c + 3) + m ≤ s.size) {j base cnt : Nat} (hj : j < m)
    (hb : base + cnt ≤ m) (hjb : ¬(base ≤ j ∧ j < base + cnt))
    (L L' : Nat → Nat → Float → Float)
    (hdiag : ∀ c', c ≤ c' → c' < c + 4 → ∀ v,
      d.apply (L j c' s[off + ld * c' + j]!) A.data[A.off + A.ld * j + j]! = L' j c' v)
    (hrow : ∀ c', c ≤ c' → c' < c + 4 → ∀ i, base ≤ i → i < base + cnt → ∀ v,
      L' i c' v = L i c' v - L' j c' 0 * A.data[A.off + A.ld * j + i]!)
    (hsame : ∀ c', c ≤ c' → c' < c + 4 → ∀ i, i < m → i ≠ j → ¬(base ≤ i ∧ i < base + cnt) →
      ∀ v, L' i c' v = L i c' v) :
    stepRows4 d A (off + ld * c) (off + ld * (c + 1)) (off + ld * (c + 2)) (off + ld * (c + 3)) j
        base cnt (mapMat s off ld m c (c + 4) L) = mapMat s off ld m c (c + 4) L' := by
  have hq' : ∀ q, q < 4 → off + ld * (c + q) + m ≤ s.size := fun q hq4 => by
    have := Nat.mul_le_mul_left ld (show c + q ≤ c + 3 by lia); lia
  have hc : ∀ q, q < 4 → c ≤ c + q ∧ c + q < c + 4 := fun q hq4 => ⟨by lia, by lia⟩
  let T := fun k => L' j k 0
  have ht : ∀ q, q < 4 → d.apply (mapMat s off ld m c (c + 4) L)[off + ld * (c + q) + j]!
      A.data[A.off + A.ld * j + j]! = T (c + q) := fun q hq4 => by
    rw [getElem!_mapMat_col s off ld c (c + 4) _ hml (hc q hq4) hj (by have := hq' q hq4; lia)]
    exact hdiag (c + q) (hc q hq4).1 (hc q hq4).2 0
  have ht₀ := ht 0 (by lia)
  simp only [Nat.add_zero] at ht₀
  unfold stepRows4
  simp only [ht₀, ht 1 (by lia), ht 2 (by lia), ht 3 (by lia)]
  rw [set!_mapMat_col s off ld hml ⟨Nat.le_refl c, by lia⟩ hj,
    set!_mapMat_col s off ld hml (hc 1 (by lia)) hj,
    set!_mapMat_col s off ld hml (hc 2 (by lia)) hj,
    set!_mapMat_col s off ld hml (hc 3 (by lia)) hj]
  -- The rows `base + k` to `base + cnt - 1` are still `L`, the others are `L'`.
  let P := fun k i c' v => if base + k ≤ i ∧ i < base + cnt then L i c' v else L' i c' v
  have hP : ∀ k, k ≤ cnt →
      iterRange (fun i s' => rowSub4 (off + ld * c) (off + ld * (c + 1)) (off + ld * (c + 2))
        (off + ld * (c + 3)) (base + i) (T c) (T (c + 1)) (T (c + 2)) (T (c + 3))
        A.data[A.off + A.ld * j + (base + i)]! s') 0 k
        (mapMat s off ld m c (c + 4) fun i k v =>
          if k = c + 3 ∧ j ≤ i ∧ i < j + 1 then T (c + 3) else
          if k = c + 2 ∧ j ≤ i ∧ i < j + 1 then T (c + 2) else
          if k = c + 1 ∧ j ≤ i ∧ i < j + 1 then T (c + 1) else
          if k = c ∧ j ≤ i ∧ i < j + 1 then T c else L i k v) =
        mapMat s off ld m c (c + 4) (P k) := by
    intro k hk
    induction k with
    | zero =>
      rw [iterRange_self]
      apply mapMat_congr
      intro i c' v hi h₁ h₂
      simp only [P]
      by_cases hij : i = j
      · subst hij
        have e := hdiag c' h₁ h₂
        have hc' : c' = c ∨ c' = c + 1 ∨ c' = c + 2 ∨ c' = c + 3 := by lia
        rcases hc' with rfl | rfl | rfl | rfl <;> simp [T, hjb] <;>
          exact (e 0).symm.trans (e v)
      · by_cases hr : base ≤ i ∧ i < base + cnt
        · simp [show ¬ (j ≤ i ∧ i < j + 1) by lia, hr]
        · rw [hsame c' h₁ h₂ i hi hij hr]
          simp [show ¬ (j ≤ i ∧ i < j + 1) by lia]
    | succ k ih =>
      rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
      have hr : base + k < m := by lia
      have hp : ∀ q, q < 4 → off + ld * (c + q) + (base + k) < s.size := fun q hq4 => by
        have := hq' q hq4; lia
      have hp₀ := hp 0 (by lia)
      simp only [Nat.add_zero] at hp₀
      unfold rowSub4
      rw [set!_mapMat_col_fun s off ld hml ⟨Nat.le_refl c, by lia⟩ hr hp₀ _
          (fun w => w - T c * A.data[A.off + A.ld * j + (base + k)]!)
          (by rw [getElem!_mapMat_col s off ld c (c + 4) _ hml ⟨Nat.le_refl c, by lia⟩ hr hp₀]),
        set!_mapMat_col_fun s off ld hml (hc 1 (by lia)) hr (hp 1 (by lia)) _
          (fun w => w - T (c + 1) * A.data[A.off + A.ld * j + (base + k)]!)
          (by rw [getElem!_mapMat_col s off ld c (c + 4) _ hml (hc 1 (by lia)) hr (hp 1 (by lia))]
              simp [P, show base + k < base + cnt by lia]),
        set!_mapMat_col_fun s off ld hml (hc 2 (by lia)) hr (hp 2 (by lia)) _
          (fun w => w - T (c + 2) * A.data[A.off + A.ld * j + (base + k)]!)
          (by rw [getElem!_mapMat_col s off ld c (c + 4) _ hml (hc 2 (by lia)) hr (hp 2 (by lia))]
              simp [P, show base + k < base + cnt by lia]),
        set!_mapMat_col_fun s off ld hml (hc 3 (by lia)) hr (hp 3 (by lia)) _
          (fun w => w - T (c + 3) * A.data[A.off + A.ld * j + (base + k)]!)
          (by rw [getElem!_mapMat_col s off ld c (c + 4) _ hml (hc 3 (by lia)) hr (hp 3 (by lia))]
              simp [P, show base + k < base + cnt by lia])]
      apply mapMat_congr
      intro i c' v hi h₁ h₂
      by_cases hik : i = base + k
      · subst hik
        have e := hrow c' h₁ h₂ (base + k) (by lia) (by lia) v
        have hc' : c' = c ∨ c' = c + 1 ∨ c' = c + 2 ∨ c' = c + 3 := by lia
        rcases hc' with rfl | rfl | rfl | rfl <;>
          simp [P, e, T, show ¬ base + (k + 1) ≤ base + k by lia, show k < cnt by lia]
      · by_cases hk' : base + (k + 1) ≤ i ∧ i < base + cnt
        · simp [P, hk', show base + k ≤ i by lia, show ¬ i < base + k + 1 by lia]
        · simp [P, hk', show ¬ (base + k ≤ i ∧ i < base + cnt) by lia,
            show ¬ (base + k ≤ i ∧ i < base + k + 1) by lia]
  rw [hP _ (Nat.le_refl _)]
  apply mapMat_congr
  intro i c' v hi _ _
  simp only [P]
  rw [ite_eq_right (by lia)]

/-- The value of the lower solve of column `c` of a matrix in `s`, after the steps `l < t`. -/
def lowerColAt (d : Diag) (A : Mat m m) (s : Float64Array) (off ld t : Nat) (i c : Nat)
    (v : Float) : Float :=
  if h : off + ld * c + m ≤ s.size then lowerAt d A (colAt s (off + ld * c) h) t i v else v

private theorem lowerColAt_diag (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat)
    {c j : Nat} (hq : off + ld * c + m ≤ s.size) (hj : j < m) (v : Float) :
    d.apply (lowerColAt d A s off ld j j c s[off + ld * c + j]!) A.data[A.off + A.ld * j + j]! =
      lowerColAt d A s off ld (j + 1) j c v := by
  have hx := (colAt (m := m) s (off + ld * c) hq).index_lt hj
  simp only [lowerColAt, dite_eq_left hq, lowerAt, Nat.lt_irrefl, ite_false,
    show j < j + 1 by lia, ite_true]
  rw [trsvLower_eq d A _ hj, Vec.getElem_def,
    ← getElem!_pos (colAt (m := m) s (off + ld * c) hq).data _ hx, Mat.getElem_def,
    ← getElem!_pos A.data _ (A.index_lt hj hj)]
  simp only [colAt, Nat.one_mul]
  congr 2
  funext l hl s'
  rw [Mat.getElem_def, getElem!_pos A.data _ (A.index_lt hj (by lia))]

private theorem lowerColAt_below (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat)
    {c j i : Nat} (hq : off + ld * c + m ≤ s.size) (hji : j < i) (v : Float) :
    lowerColAt d A s off ld (j + 1) i c v =
      lowerColAt d A s off ld j i c v -
        lowerColAt d A s off ld (j + 1) j c 0 * A.data[A.off + A.ld * j + i]! := by
  simp [lowerColAt, dite_eq_left hq, lowerAt, show ¬i < j + 1 by lia, show ¬i < j by lia,
    Nat.fold_succ]

private theorem lowerColAt_above (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat)
    {c j i : Nat} (hq : off + ld * c + m ≤ s.size) (hij : i < j) (v : Float) :
    lowerColAt d A s off ld (j + 1) i c v = lowerColAt d A s off ld j i c v := by
  simp [lowerColAt, dite_eq_left hq, lowerAt, hij, show i < j + 1 by lia]

/-- Step `j` of the lower solve of four columns: their elements `j + 1` to `m - 1` get its terms. -/
abbrev step4 (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ j : Nat) (b : Float64Array) : Float64Array :=
  stepRows4 d A o₀ o₁ o₂ o₃ j (j + 1) (m - j - 1) b

/-- `step4` on four columns of a `mapMat` with the steps `l < j` of their solves. -/
theorem step4_mapMat (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat) (hml : m ≤ ld)
    (c : Nat) (hq : off + ld * (c + 3) + m ≤ s.size) {j : Nat} (hj : j < m) :
    step4 d A (off + ld * c) (off + ld * (c + 1)) (off + ld * (c + 2)) (off + ld * (c + 3)) j
        (mapMat s off ld m c (c + 4) (lowerColAt d A s off ld j)) =
      mapMat s off ld m c (c + 4) (lowerColAt d A s off ld (j + 1)) := by
  have hcol : ∀ c', c ≤ c' → c' < c + 4 → off + ld * c' + m ≤ s.size := fun c' h₁ h₂ => by
    have := Nat.mul_le_mul_left ld (show c' ≤ c + 3 by lia); lia
  apply stepRows4_mapMat d A s off ld hml c hq hj (by lia) (by lia)
  · exact fun c' h₁ h₂ v => lowerColAt_diag d A s off ld (hcol c' h₁ h₂) hj v
  · exact fun c' h₁ h₂ i h₃ _ v => lowerColAt_below d A s off ld (hcol c' h₁ h₂) (by lia) v
  · exact fun c' h₁ h₂ i hi h₃ h₄ v => lowerColAt_above d A s off ld (hcol c' h₁ h₂) (by lia) v

theorem iterRange_step4 (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat)
    (hml : m ≤ ld) (c : Nat) (hq : off + ld * (c + 3) + m ≤ s.size) {t : Nat} (ht : t ≤ m) :
    iterRange (step4 d A (off + ld * c) (off + ld * (c + 1)) (off + ld * (c + 2))
        (off + ld * (c + 3))) 0 t s =
      mapMat s off ld m c (c + 4) (lowerColAt d A s off ld t) := by
  induction t with
  | zero =>
    rw [iterRange_self]
    conv => lhs; rw [← mapMat_id s off ld m c (c + 4)]
    apply mapMat_congr
    intro i c' v _ _ _
    simp only [lowerColAt, lowerAt]
    split <;> simp
  | succ t ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), step4_mapMat d A s off ld hml c hq (by lia)]


private theorem toNat_col {off ld c : Nat} (h : off + ld * c < USize.size) :
    (off + ld * c).toUSize.toNat = off + ld * c := by grind

/--
The array of `trsm` on the lower triangle, for the four columns `c` to `c + 3` of the matrix at
the offset `off` with the leading dimension `ld` in the array `b`: it scales the columns by `α`,
then solves them together. At step `j`, it solves for their four elements `j`, then updates the
elements below them a row of the four at a time, so that it reads each element of column `j` of `A`
once for the four columns. Each element gets the operations of `trsv`, in the same order.
-/
def trsmLower4Data (d : Diag) (α : Float) (A : Mat m m) (off ld : Nat) (b : Float64Array)
    (c : Nat) (hq : off + ld * (c + 3) + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) : Float64Array :=
  let sz := b.size
  let mu := m.toUSize
  have hmu : mu.toNat = m := by grind
  have hq' : ∀ q, q < 4 → off + ld * (c + q) + m ≤ sz := fun q hq4 => by
    have := Nat.mul_le_mul_left ld (show c + q ≤ c + 3 by lia); lia
  let c₀ := (off + ld * c).toUSize
  have h₀ : c₀.toNat + m ≤ sz := by
    have := hq' 0 (by lia); rw [Nat.add_zero] at this; rw [toNat_col (by lia)]; exact this
  let c₁ := (off + ld * (c + 1)).toUSize
  have h₁ : c₁.toNat + m ≤ sz := by have := hq' 1 (by lia); rw [toNat_col (by lia)]; exact this
  let c₂ := (off + ld * (c + 2)).toUSize
  have h₂ : c₂.toNat + m ≤ sz := by have := hq' 2 (by lia); rw [toNat_col (by lia)]; exact this
  let c₃ := (off + ld * (c + 3)).toUSize
  have h₃ : c₃.toNat + m ≤ sz := by have := hq' 3 (by lia); rw [toNat_col (by lia)]; exact this
  b.runInPlaceThenOf sz rfl
    (colScaleT α mu hmu c₀ h₀ (colScaleT α mu hmu c₁ h₁ (colScaleT α mu hmu c₂ h₂
      (colScaleT α mu hmu c₃ h₃
        (Tail.forInFrom 0 mu 0 (Nat.le_refl _) () (fun j _ hj next _ =>
          Tail.readThen (c₀ + j) (col_lt h₀ (hmu ▸ hj)) fun v₀ =>
          Tail.readThen (c₁ + j) (col_lt h₁ (hmu ▸ hj)) fun v₁ =>
          Tail.readThen (c₂ + j) (col_lt h₂ (hmu ▸ hj)) fun v₂ =>
          Tail.readThen (c₃ + j) (col_lt h₃ (hmu ▸ hj)) fun v₃ =>
          let ajj := A.uget _ _ rfl rfl hs.1 j j (hmu ▸ hj) (hmu ▸ hj)
          let t₀ := d.apply v₀ ajj
          let t₁ := d.apply v₁ ajj
          let t₂ := d.apply v₂ ajj
          let t₃ := d.apply v₃ ajj
          Tail.writeThen (c₀ + j) (col_lt h₀ (hmu ▸ hj)) t₀ <|
          Tail.writeThen (c₁ + j) (col_lt h₁ (hmu ▸ hj)) t₁ <|
          Tail.writeThen (c₂ + j) (col_lt h₂ (hmu ▸ hj)) t₂ <|
          Tail.writeThen (c₃ + j) (col_lt h₃ (hmu ▸ hj)) t₃ <|
          Tail.forInFrom 0 (mu - j - 1) 0 (Nat.le_refl _) () (fun i _ hi next' _ =>
            Tail.readThen (c₀ + (j + 1 + i)) (col_below_lt h₀ hmu (hmu ▸ hj) hi) fun w₀ =>
            Tail.readThen (c₁ + (j + 1 + i)) (col_below_lt h₁ hmu (hmu ▸ hj) hi) fun w₁ =>
            Tail.readThen (c₂ + (j + 1 + i)) (col_below_lt h₂ hmu (hmu ▸ hj) hi) fun w₂ =>
            Tail.readThen (c₃ + (j + 1 + i)) (col_below_lt h₃ hmu (hmu ▸ hj) hi) fun w₃ =>
            let aij := A.uget _ _ rfl rfl hs.1 (j + 1 + i) j (below_lt hmu (hmu ▸ hj) hi)
              (hmu ▸ hj)
            Tail.writeThen (c₀ + (j + 1 + i)) (col_below_lt h₀ hmu (hmu ▸ hj) hi) (w₀ - t₀ * aij) <|
            Tail.writeThen (c₁ + (j + 1 + i)) (col_below_lt h₁ hmu (hmu ▸ hj) hi) (w₁ - t₁ * aij) <|
            Tail.writeThen (c₂ + (j + 1 + i)) (col_below_lt h₂ hmu (hmu ▸ hj) hi) (w₂ - t₂ * aij) <|
            Tail.writeThen (c₃ + (j + 1 + i)) (col_below_lt h₃ hmu (hmu ▸ hj) hi) (w₃ - t₃ * aij)
              (next' ()))
            fun _ => next ())
          fun _ => Tail.done () fun _ a _ => a)))))

/-- The columns `c` to `c + 3` of `b`, scaled by `α`. -/
theorem scale4_eq (α : Float) (b : Float64Array) (off ld : Nat) (hml : m ≤ ld) (c : Nat) :
    ((((b.modifyAt (Stride.mk (off + ld * c) 1).idx 0 m fun _ v => α * v).modifyAt
        (Stride.mk (off + ld * (c + 1)) 1).idx 0 m fun _ v => α * v).modifyAt
        (Stride.mk (off + ld * (c + 2)) 1).idx 0 m fun _ v => α * v).modifyAt
        (Stride.mk (off + ld * (c + 3)) 1).idx 0 m fun _ v => α * v) =
      mapMat b off ld m c (c + 4) fun _ _ v => α * v := by
  conv => lhs; rw [← mapMat_id b off ld m c (c + 4)]
  rw [modifyAt_col_mapMat_mid _ _ _ hml ⟨Nat.le_refl _, by lia⟩ (Nat.le_refl _),
    modifyAt_col_mapMat_mid _ _ _ hml ⟨by lia, by lia⟩ (Nat.le_refl _),
    modifyAt_col_mapMat_mid _ _ _ hml ⟨by lia, by lia⟩ (Nat.le_refl _),
    modifyAt_col_mapMat_mid _ _ _ hml ⟨by lia, by lia⟩ (Nat.le_refl _)]
  apply mapMat_congr
  intro i c' v hi h₁ h₂
  have hc' : c' = c ∨ c' = c + 1 ∨ c' = c + 2 ∨ c' = c + 3 := by lia
  rcases hc' with rfl | rfl | rfl | rfl <;> simp [hi]

theorem trsmLower4Data_eq (d : Diag) (α : Float) (A : Mat m m) (off ld : Nat) (hml : m ≤ ld)
    (b : Float64Array) (c : Nat) (hq : off + ld * (c + 3) + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    trsmLower4Data d α A off ld b c hq hs =
      mapMat (mapMat b off ld m c (c + 4) fun _ _ v => α * v) off ld m c (c + 4)
        (lowerColAt d A (mapMat b off ld m c (c + 4) fun _ _ v => α * v) off ld m) := by
  have hq' : ∀ q, q < 4 → off + ld * (c + q) + m ≤ b.size := fun q hq4 => by
    have := Nat.mul_le_mul_left ld (show c + q ≤ c + 3 by lia); lia
  have e₀ := toNat_col (off := off) (ld := ld) (c := c) (by have := hq' 0 (by lia); lia)
  have e₁ := toNat_col (off := off) (ld := ld) (c := c + 1) (by have := hq' 1 (by lia); lia)
  have e₂ := toNat_col (off := off) (ld := ld) (c := c + 2) (by have := hq' 2 (by lia); lia)
  have e₃ := toNat_col (off := off) (ld := ld) (c := c + 3) (by have := hq' 3 (by lia); lia)
  have hmu : m.toUSize.toNat = m := by grind
  unfold trsmLower4Data
  simp only [runInPlaceThenOf_eq]
  rw [run_colScaleT _ _ _ _ _ hs.2, run_colScaleT _ _ _ _ _ hs.2, run_colScaleT _ _ _ _ _ hs.2,
    run_colScaleT _ _ _ _ _ hs.2]
  rw [Tail.run_forInFrom_unit (F := step4 d A (off + ld * c) (off + ld * (c + 1))
    (off + ld * (c + 2)) (off + ld * (c + 3))) (hF := fun _ _ => size_stepRows4 ..)]
  · simp only [Tail.run_done, USize.toNat_zero, hmu, e₀, e₁, e₂, e₃]
    rw [scale4_eq α b off ld hml c]
    exact iterRange_step4 d A _ off ld hml c (by simpa using hq) (Nat.le_refl _)
  · intro j _ hj next a h
    rw [hmu] at hj
    have hr : (m.toUSize - j - 1).toNat = m - j.toNat - 1 := by grind
    have hbs : b.size < USize.size := hs.2
    have hcj : ∀ (cq : USize) (i : Nat), cq.toNat + m ≤ b.size → i < m →
        ∀ u : USize, u.toNat = i → (cq + u).toNat = cq.toNat + i := by
      intro cq i hw hi u hu; grind
    have q₀ : ((off + ld * c).toUSize + j).toNat = off + ld * c + j.toNat := by
      rw [hcj _ _ (by have := hq' 0 (by lia); rw [e₀]; simpa using this) hj j rfl, e₀]
    have q₁ : ((off + ld * (c + 1)).toUSize + j).toNat = off + ld * (c + 1) + j.toNat := by
      rw [hcj _ _ (by have := hq' 1 (by lia); rw [e₁]; exact this) hj j rfl, e₁]
    have q₂ : ((off + ld * (c + 2)).toUSize + j).toNat = off + ld * (c + 2) + j.toNat := by
      rw [hcj _ _ (by have := hq' 2 (by lia); rw [e₂]; exact this) hj j rfl, e₂]
    have q₃ : ((off + ld * (c + 3)).toUSize + j).toNat = off + ld * (c + 3) + j.toNat := by
      rw [hcj _ _ (by have := hq' 3 (by lia); rw [e₃]; exact this) hj j rfl, e₃]
    simp only [Tail.run_readThen, Tail.run_writeThen]
    rw [Tail.run_forInFrom_unit (F := fun i s => rowSub4 (off + ld * c) (off + ld * (c + 1))
      (off + ld * (c + 2)) (off + ld * (c + 3)) (j.toNat + 1 + i)
      (d.apply a[off + ld * c + j.toNat]! A.data[A.off + A.ld * j.toNat + j.toNat]!)
      (d.apply a[off + ld * (c + 1) + j.toNat]! A.data[A.off + A.ld * j.toNat + j.toNat]!)
      (d.apply a[off + ld * (c + 2) + j.toNat]! A.data[A.off + A.ld * j.toNat + j.toNat]!)
      (d.apply a[off + ld * (c + 3) + j.toNat]! A.data[A.off + A.ld * j.toNat + j.toNat]!)
      A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + i)]! s)
      (hF := fun _ _ => by simp [rowSub4])]
    · apply run_congr
      simp only [step4, stepRows4, hr, q₀, q₁, q₂, q₃, set_eq_set!, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def, USize.toNat_zero]
    · intro i _ hi next' s' h'
      rw [hr] at hi
      have hb : j.toNat + 1 + i.toNat < m := by lia
      have hji : (j + 1 + i).toNat = j.toNat + 1 + i.toNat :=
        toNat_succ_add (Nat.lt_of_lt_of_le hb (by have := hq' 0 (by lia); lia))
      have p₀ : ((off + ld * c).toUSize + (j + 1 + i)).toNat =
          off + ld * c + (j.toNat + 1 + i.toNat) := by
        rw [hcj _ _ (by have := hq' 0 (by lia); rw [e₀]; simpa using this) hb _ hji, e₀]
      have p₁ : ((off + ld * (c + 1)).toUSize + (j + 1 + i)).toNat =
          off + ld * (c + 1) + (j.toNat + 1 + i.toNat) := by
        rw [hcj _ _ (by have := hq' 1 (by lia); rw [e₁]; exact this) hb _ hji, e₁]
      have p₂ : ((off + ld * (c + 2)).toUSize + (j + 1 + i)).toNat =
          off + ld * (c + 2) + (j.toNat + 1 + i.toNat) := by
        rw [hcj _ _ (by have := hq' 2 (by lia); rw [e₂]; exact this) hb _ hji, e₂]
      have p₃ : ((off + ld * (c + 3)).toUSize + (j + 1 + i)).toNat =
          off + ld * (c + 3) + (j.toNat + 1 + i.toNat) := by
        rw [hcj _ _ (by have := hq' 3 (by lia); rw [e₃]; exact this) hb _ hji, e₃]
      simp only [Tail.run_readThen, Tail.run_writeThen]
      apply run_congr
      simp only [rowSub4, p₀, p₁, p₂, p₃, q₀, q₁, q₂, q₃, hji, set_eq_set!, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def]


/-! ### The upper triangle -/

/--
The value of the upper solve of `x` after the steps `t < k`, at the element `i` of old value `v`:
solved for `i ≥ m - k`, and with the terms of the steps `t < k` otherwise.
-/
def upperAt (d : Diag) (A : Mat m m) (x : Vec m) (k i : Nat) (v : Float) : Float :=
  if m - k ≤ i then trsvUpper d A x i
  else Nat.fold k (fun t _ s =>
    s - trsvUpper d A x (m - 1 - t) * A.data[A.off + A.ld * (m - 1 - t) + i]!) v

/-- The value of the upper solve of column `c` of a matrix in `s`, after the steps `t < k`. -/
def upperColAt (d : Diag) (A : Mat m m) (s : Float64Array) (off ld k : Nat) (i c : Nat)
    (v : Float) : Float :=
  if h : off + ld * c + m ≤ s.size then upperAt d A (colAt s (off + ld * c) h) k i v else v

private theorem upperColAt_diag (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat)
    {c k : Nat} (hq : off + ld * c + m ≤ s.size) (hk : k < m) (v : Float) :
    d.apply (upperColAt d A s off ld k (m - 1 - k) c s[off + ld * c + (m - 1 - k)]!)
        A.data[A.off + A.ld * (m - 1 - k) + (m - 1 - k)]! =
      upperColAt d A s off ld (k + 1) (m - 1 - k) c v := by
  have hx := (colAt (m := m) s (off + ld * c) hq).index_lt (show m - 1 - k < m by lia)
  simp only [upperColAt, dite_eq_left hq, upperAt, show ¬m - k ≤ m - 1 - k by lia, ite_false,
    show m - (k + 1) ≤ m - 1 - k by lia, ite_true]
  rw [trsvUpper_eq d A _ (show m - 1 - k < m by lia), Vec.getElem_def,
    ← getElem!_pos (colAt (m := m) s (off + ld * c) hq).data _ hx, Mat.getElem_def,
    ← getElem!_pos A.data _ (A.index_lt (by lia) (by lia))]
  simp only [colAt, Nat.one_mul]
  rw [Nat.fold_congr (show m - 1 - (m - 1 - k) = k by lia)]
  congr 2
  funext t ht s'
  rw [Mat.getElem_def, getElem!_pos A.data _ (A.index_lt (by lia) (by lia))]

private theorem upperColAt_above (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat)
    {c k i : Nat} (hq : off + ld * c + m ≤ s.size) (hk : k < m) (hi : i < m - 1 - k) (v : Float) :
    upperColAt d A s off ld (k + 1) i c v =
      upperColAt d A s off ld k i c v -
        upperColAt d A s off ld (k + 1) (m - 1 - k) c 0 *
          A.data[A.off + A.ld * (m - 1 - k) + i]! := by
  simp [upperColAt, dite_eq_left hq, upperAt, show ¬m - (k + 1) ≤ i by lia, show ¬m - k ≤ i by lia,
    show m - (k + 1) ≤ m - 1 - k by lia, Nat.fold_succ]

private theorem upperColAt_below (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat)
    {c k i : Nat} (hq : off + ld * c + m ≤ s.size) (hi : m - k ≤ i) (v : Float) :
    upperColAt d A s off ld (k + 1) i c v = upperColAt d A s off ld k i c v := by
  simp [upperColAt, dite_eq_left hq, upperAt, hi, show m - (k + 1) ≤ i by lia]

/--
Step `k` of the upper solve of four columns: their elements `0` to `m - 2 - k` get the terms of
the elements `m - 1 - k`.
-/
abbrev stepU4 (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ k : Nat) (b : Float64Array) : Float64Array :=
  stepRows4 d A o₀ o₁ o₂ o₃ (m - 1 - k) 0 (m - 1 - k) b

/-- `stepU4` on four columns of a `mapMat` with the steps `t < k` of their solves. -/
theorem stepU4_mapMat (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat) (hml : m ≤ ld)
    (c : Nat) (hq : off + ld * (c + 3) + m ≤ s.size) {k : Nat} (hk : k < m) :
    stepU4 d A (off + ld * c) (off + ld * (c + 1)) (off + ld * (c + 2)) (off + ld * (c + 3)) k
        (mapMat s off ld m c (c + 4) (upperColAt d A s off ld k)) =
      mapMat s off ld m c (c + 4) (upperColAt d A s off ld (k + 1)) := by
  have hcol : ∀ c', c ≤ c' → c' < c + 4 → off + ld * c' + m ≤ s.size := fun c' h₁ h₂ => by
    have := Nat.mul_le_mul_left ld (show c' ≤ c + 3 by lia); lia
  apply stepRows4_mapMat d A s off ld hml c hq (show m - 1 - k < m by lia) (by lia) (by lia)
  · exact fun c' h₁ h₂ v => upperColAt_diag d A s off ld (hcol c' h₁ h₂) hk v
  · exact fun c' h₁ h₂ i _ h₄ v => upperColAt_above d A s off ld (hcol c' h₁ h₂) hk (by lia) v
  · exact fun c' h₁ h₂ i hi h₃ h₄ v => upperColAt_below d A s off ld (hcol c' h₁ h₂) (by lia) v

theorem iterRange_stepU4 (d : Diag) (A : Mat m m) (s : Float64Array) (off ld : Nat)
    (hml : m ≤ ld) (c : Nat) (hq : off + ld * (c + 3) + m ≤ s.size) {t : Nat} (ht : t ≤ m) :
    iterRange (stepU4 d A (off + ld * c) (off + ld * (c + 1)) (off + ld * (c + 2))
        (off + ld * (c + 3))) 0 t s =
      mapMat s off ld m c (c + 4) (upperColAt d A s off ld t) := by
  induction t with
  | zero =>
    rw [iterRange_self]
    conv => lhs; rw [← mapMat_id s off ld m c (c + 4)]
    apply mapMat_congr
    intro i c' v hi _ _
    simp only [upperColAt, upperAt]
    split <;> simp [show ¬m ≤ i by lia]
  | succ t ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), stepU4_mapMat d A s off ld hml c hq (by lia)]

private theorem top_lt {mu k : USize} (hmu : mu.toNat = m) (hk : k.toNat < m) :
    (mu - 1 - k).toNat < m := by
  have : (mu - 1 - k).toNat = m - 1 - k.toNat := by grind
  lia

private theorem above_lt {mu k i : USize} (hmu : mu.toNat = m) (hk : k.toNat < m)
    (hi : i.toNat < (mu - 1 - k).toNat) : i.toNat < m :=
  Nat.lt_trans hi (top_lt hmu hk)

/--
The array of `trsm` on the upper triangle, for the four columns `c` to `c + 3` of the matrix at
the offset `off` with the leading dimension `ld` in the array `b`, as `trsmLower4Data`: at step
`k`, it solves for their four elements `j = m - 1 - k`, then updates the elements above them a row
of the four at a time.
-/
def trsmUpper4Data (d : Diag) (α : Float) (A : Mat m m) (off ld : Nat) (b : Float64Array)
    (c : Nat) (hq : off + ld * (c + 3) + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) : Float64Array :=
  let sz := b.size
  let mu := m.toUSize
  have hmu : mu.toNat = m := by grind
  have hq' : ∀ q, q < 4 → off + ld * (c + q) + m ≤ sz := fun q hq4 => by
    have := Nat.mul_le_mul_left ld (show c + q ≤ c + 3 by lia); lia
  let c₀ := (off + ld * c).toUSize
  have h₀ : c₀.toNat + m ≤ sz := by
    have := hq' 0 (by lia); rw [Nat.add_zero] at this; rw [toNat_col (by lia)]; exact this
  let c₁ := (off + ld * (c + 1)).toUSize
  have h₁ : c₁.toNat + m ≤ sz := by have := hq' 1 (by lia); rw [toNat_col (by lia)]; exact this
  let c₂ := (off + ld * (c + 2)).toUSize
  have h₂ : c₂.toNat + m ≤ sz := by have := hq' 2 (by lia); rw [toNat_col (by lia)]; exact this
  let c₃ := (off + ld * (c + 3)).toUSize
  have h₃ : c₃.toNat + m ≤ sz := by have := hq' 3 (by lia); rw [toNat_col (by lia)]; exact this
  b.runInPlaceThenOf sz rfl
    (colScaleT α mu hmu c₀ h₀ (colScaleT α mu hmu c₁ h₁ (colScaleT α mu hmu c₂ h₂
      (colScaleT α mu hmu c₃ h₃
        (Tail.forInFrom 0 mu 0 (Nat.le_refl _) () (fun k _ hk next _ =>
          let j := mu - 1 - k
          have hj : j.toNat < m := top_lt hmu (hmu ▸ hk)
          Tail.readThen (c₀ + j) (col_lt h₀ hj) fun v₀ =>
          Tail.readThen (c₁ + j) (col_lt h₁ hj) fun v₁ =>
          Tail.readThen (c₂ + j) (col_lt h₂ hj) fun v₂ =>
          Tail.readThen (c₃ + j) (col_lt h₃ hj) fun v₃ =>
          let ajj := A.uget _ _ rfl rfl hs.1 j j hj hj
          let t₀ := d.apply v₀ ajj
          let t₁ := d.apply v₁ ajj
          let t₂ := d.apply v₂ ajj
          let t₃ := d.apply v₃ ajj
          Tail.writeThen (c₀ + j) (col_lt h₀ hj) t₀ <|
          Tail.writeThen (c₁ + j) (col_lt h₁ hj) t₁ <|
          Tail.writeThen (c₂ + j) (col_lt h₂ hj) t₂ <|
          Tail.writeThen (c₃ + j) (col_lt h₃ hj) t₃ <|
          Tail.forInFrom 0 j 0 (Nat.le_refl _) () (fun i _ hi next' _ =>
            have hi' : i.toNat < m := above_lt hmu (hmu ▸ hk) hi
            Tail.readThen (c₀ + i) (col_lt h₀ hi') fun w₀ =>
            Tail.readThen (c₁ + i) (col_lt h₁ hi') fun w₁ =>
            Tail.readThen (c₂ + i) (col_lt h₂ hi') fun w₂ =>
            Tail.readThen (c₃ + i) (col_lt h₃ hi') fun w₃ =>
            let aij := A.uget _ _ rfl rfl hs.1 i j hi' hj
            Tail.writeThen (c₀ + i) (col_lt h₀ hi') (w₀ - t₀ * aij) <|
            Tail.writeThen (c₁ + i) (col_lt h₁ hi') (w₁ - t₁ * aij) <|
            Tail.writeThen (c₂ + i) (col_lt h₂ hi') (w₂ - t₂ * aij) <|
            Tail.writeThen (c₃ + i) (col_lt h₃ hi') (w₃ - t₃ * aij) (next' ()))
            fun _ => next ())
          fun _ => Tail.done () fun _ a _ => a)))))

theorem trsmUpper4Data_eq (d : Diag) (α : Float) (A : Mat m m) (off ld : Nat) (hml : m ≤ ld)
    (b : Float64Array) (c : Nat) (hq : off + ld * (c + 3) + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    trsmUpper4Data d α A off ld b c hq hs =
      mapMat (mapMat b off ld m c (c + 4) fun _ _ v => α * v) off ld m c (c + 4)
        (upperColAt d A (mapMat b off ld m c (c + 4) fun _ _ v => α * v) off ld m) := by
  have hq' : ∀ q, q < 4 → off + ld * (c + q) + m ≤ b.size := fun q hq4 => by
    have := Nat.mul_le_mul_left ld (show c + q ≤ c + 3 by lia); lia
  have e₀ := toNat_col (off := off) (ld := ld) (c := c) (by have := hq' 0 (by lia); lia)
  have e₁ := toNat_col (off := off) (ld := ld) (c := c + 1) (by have := hq' 1 (by lia); lia)
  have e₂ := toNat_col (off := off) (ld := ld) (c := c + 2) (by have := hq' 2 (by lia); lia)
  have e₃ := toNat_col (off := off) (ld := ld) (c := c + 3) (by have := hq' 3 (by lia); lia)
  have hmu : m.toUSize.toNat = m := by grind
  unfold trsmUpper4Data
  simp only [runInPlaceThenOf_eq]
  rw [run_colScaleT _ _ _ _ _ hs.2, run_colScaleT _ _ _ _ _ hs.2, run_colScaleT _ _ _ _ _ hs.2,
    run_colScaleT _ _ _ _ _ hs.2]
  rw [Tail.run_forInFrom_unit (F := stepU4 d A (off + ld * c) (off + ld * (c + 1))
    (off + ld * (c + 2)) (off + ld * (c + 3))) (hF := fun _ _ => size_stepRows4 ..)]
  · simp only [Tail.run_done, USize.toNat_zero, hmu, e₀, e₁, e₂, e₃]
    rw [scale4_eq α b off ld hml c]
    exact iterRange_stepU4 d A _ off ld hml c (by simpa using hq) (Nat.le_refl _)
  · intro k _ hk next a h
    rw [hmu] at hk
    have hr : (m.toUSize - 1 - k).toNat = m - 1 - k.toNat := by grind
    have hj : m - 1 - k.toNat < m := by lia
    have hbs : b.size < USize.size := hs.2
    have hcj : ∀ (cq : USize) (i : Nat), cq.toNat + m ≤ b.size → i < m →
        ∀ u : USize, u.toNat = i → (cq + u).toNat = cq.toNat + i := by
      intro cq i hw hi u hu; grind
    have q₀ : ((off + ld * c).toUSize + (m.toUSize - 1 - k)).toNat =
        off + ld * c + (m - 1 - k.toNat) := by
      rw [hcj _ _ (by have := hq' 0 (by lia); rw [e₀]; simpa using this) hj _ hr, e₀]
    have q₁ : ((off + ld * (c + 1)).toUSize + (m.toUSize - 1 - k)).toNat =
        off + ld * (c + 1) + (m - 1 - k.toNat) := by
      rw [hcj _ _ (by have := hq' 1 (by lia); rw [e₁]; exact this) hj _ hr, e₁]
    have q₂ : ((off + ld * (c + 2)).toUSize + (m.toUSize - 1 - k)).toNat =
        off + ld * (c + 2) + (m - 1 - k.toNat) := by
      rw [hcj _ _ (by have := hq' 2 (by lia); rw [e₂]; exact this) hj _ hr, e₂]
    have q₃ : ((off + ld * (c + 3)).toUSize + (m.toUSize - 1 - k)).toNat =
        off + ld * (c + 3) + (m - 1 - k.toNat) := by
      rw [hcj _ _ (by have := hq' 3 (by lia); rw [e₃]; exact this) hj _ hr, e₃]
    simp only [Tail.run_readThen, Tail.run_writeThen]
    rw [Tail.run_forInFrom_unit (F := fun i s => rowSub4 (off + ld * c) (off + ld * (c + 1))
      (off + ld * (c + 2)) (off + ld * (c + 3)) (0 + i)
      (d.apply a[off + ld * c + (m - 1 - k.toNat)]!
        A.data[A.off + A.ld * (m - 1 - k.toNat) + (m - 1 - k.toNat)]!)
      (d.apply a[off + ld * (c + 1) + (m - 1 - k.toNat)]!
        A.data[A.off + A.ld * (m - 1 - k.toNat) + (m - 1 - k.toNat)]!)
      (d.apply a[off + ld * (c + 2) + (m - 1 - k.toNat)]!
        A.data[A.off + A.ld * (m - 1 - k.toNat) + (m - 1 - k.toNat)]!)
      (d.apply a[off + ld * (c + 3) + (m - 1 - k.toNat)]!
        A.data[A.off + A.ld * (m - 1 - k.toNat) + (m - 1 - k.toNat)]!)
      A.data[A.off + A.ld * (m - 1 - k.toNat) + (0 + i)]! s)
      (hF := fun _ _ => by simp [rowSub4])]
    · apply run_congr
      simp only [stepU4, stepRows4, hr, q₀, q₁, q₂, q₃, set_eq_set!, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def, USize.toNat_zero]
    · intro i _ hi next' s' h'
      rw [hr] at hi
      have hb : i.toNat < m := by lia
      have p₀ : ((off + ld * c).toUSize + i).toNat = off + ld * c + (0 + i.toNat) := by
        rw [hcj _ _ (by have := hq' 0 (by lia); rw [e₀]; simpa using this) hb _ rfl, e₀,
          Nat.zero_add]
      have p₁ : ((off + ld * (c + 1)).toUSize + i).toNat = off + ld * (c + 1) + (0 + i.toNat) := by
        rw [hcj _ _ (by have := hq' 1 (by lia); rw [e₁]; exact this) hb _ rfl, e₁, Nat.zero_add]
      have p₂ : ((off + ld * (c + 2)).toUSize + i).toNat = off + ld * (c + 2) + (0 + i.toNat) := by
        rw [hcj _ _ (by have := hq' 2 (by lia); rw [e₂]; exact this) hb _ rfl, e₂, Nat.zero_add]
      have p₃ : ((off + ld * (c + 3)).toUSize + i).toNat = off + ld * (c + 3) + (0 + i.toNat) := by
        rw [hcj _ _ (by have := hq' 3 (by lia); rw [e₃]; exact this) hb _ rfl, e₃, Nat.zero_add]
      simp only [Tail.run_readThen, Tail.run_writeThen]
      apply run_congr
      simp only [rowSub4, p₀, p₁, p₂, p₃, q₀, q₁, q₂, q₃, hr, set_eq_set!, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def, Nat.zero_add]

/-- The array of `trsm` on the triangle `uplo`, for the four columns `c` to `c + 3`. -/
def trsm4Data (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (off ld : Nat)
    (b : Float64Array) (c : Nat) (hq : off + ld * (c + 3) + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) : Float64Array :=
  match uplo with
  | .lower => trsmLower4Data d α A off ld b c hq hs
  | .upper => trsmUpper4Data d α A off ld b c hq hs

theorem size_trsm4Data (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (off ld : Nat)
    (hml : m ≤ ld) (b : Float64Array) (c : Nat) (hq : off + ld * (c + 3) + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    (trsm4Data uplo d α A off ld b c hq hs).size = b.size := by
  cases uplo
  · rw [trsm4Data, trsmUpper4Data_eq d α A off ld hml, size_mapMat, size_mapMat]
  · rw [trsm4Data, trsmLower4Data_eq d α A off ld hml, size_mapMat, size_mapMat]

/-- The four columns `j` to `j + 3 < n` of a matrix with `m > 0` rows fit in its array. -/
private theorem cols4_le {off ld sz j : Nat} {b : Float64Array}
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (hb : b.size = sz) (h4 : j + 4 ≤ n)
    (hm : 0 < m) : off + ld * (j + 3) + m ≤ b.size := by
  have := Nat.mul_le_mul_left ld (show j + 3 ≤ n - 1 by lia)
  rcases hsz with h | h | h <;> lia

/--
The loop of `trsm` over the columns from `j`, on the array `b` of an `m × n` matrix: it scales
column `j` by `α`, then solves it by `trsv`, or solves the columns `j` to `j + 3` together by
`trsm4Data` when they are in `B`. It takes the offset and the leading dimension of the
matrix rather than the matrix, which would keep a second reference to its array.
-/
public def trsmLoop (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (off ld sz : Nat)
    (hml : m ≤ ld) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (j : Nat)
    (b : Float64Array) (hb : b.size = sz) : Float64Array :=
  if hj : j < n then
    if h4 : j + 4 ≤ n ∧ 0 < m ∧ A.data.size < USize.size ∧ sz < USize.size then
      trsmLoop uplo d α A off ld sz hml hsz (j + 4)
        (trsm4Data uplo d α A off ld b j (cols4_le hsz hb h4.1 h4.2.1) ⟨h4.2.2.1, hb ▸ h4.2.2.2⟩)
        ((size_trsm4Data uplo d α A off ld hml ..).trans hb)
    else
      trsmLoop uplo d α A off ld sz hml hsz (j + 1)
        (trsvData uplo d A (colOf off ld sz hsz (Vec.scalData α (colOf off ld sz hsz b hb j hj))
          (size_scalData_colOf ..) j hj))
        (size_trsvData_colOf ..)
  else b
termination_by n - j

/-- The value at `(i, j)` of `trsm` for `α ≠ 0`, from the column `j` of the array `a`. -/
private def trsmColAt (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (a : Float64Array) (i j : Nat) (_ : Float) : Float :=
  trsvSol uplo d A (Vec.ofFn fun l : Fin m => α * a[B.off + B.ld * j + l.val]!) i

/-- A step of `trsmLoop` maps column `j` to its solution. -/
private theorem trsmLoop_step (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j < n) (b : Float64Array) (hb : b.size = B.data.size)
    (a : Float64Array) (hcol : ∀ l, l < m → b[B.off + B.ld * j + l]! = a[B.off + B.ld * j + l]!) :
    trsvData uplo d A (colOf B.off B.ld B.data.size B.bound
        (Vec.scalData α (colOf B.off B.ld B.data.size B.bound b hb j hj))
        (size_scalData_colOf α B.off B.ld B.data.size B.bound b hb j hj) j hj) =
      b.modifyAt (Stride.mk (B.off + B.ld * j) 1).idx 0 m
        (fun i v => trsmColAt uplo d α A B a i j v) := by
  rw [trsvData_eq]
  simp only [colOf, Vec.stride, Vec.scalData_eq]
  rw [modifyAt_modifyAt _ _ (col_injOn _ _ _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  unfold trsmColAt
  apply trsvSol_congr _ _ _ _ i hi
  intro l hl
  have hq : B.off + B.ld * j + l < b.size := by rw [hb]; exact B.index_lt hl hj
  rw [getElem!_index (Vec.ofFn fun l : Fin m => α * a[B.off + B.ld * j + l.val]!) hl,
    Vec.getElem_ofFn]
  dsimp only
  rw [Nat.one_mul, getElem!_modifyAt_col _ _ _ _ hl, ite_eq_left hq, hcol l hl]

/--
Four columns of `trsmLoop` on the lower triangle map the columns `j` to `j + 3` to their solutions.
-/
private theorem trsmLower4_step (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (j : Nat)
    (hq : B.off + B.ld * (j + 3) + m ≤ B.data.size)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (b : Float64Array)
    (hb : b.size = B.data.size)
    (hinv : b = mapMat B.data B.off B.ld m 0 j (trsmColAt .lower d α A B B.data)) :
    trsmLower4Data d α A B.off B.ld b j (hb ▸ hq) (hb ▸ hs) =
      mapMat B.data B.off B.ld m 0 (j + 4) (trsmColAt .lower d α A B B.data) := by
  rw [trsmLower4Data_eq _ _ _ _ _ B.le_ld, mapMat_mapMat,
    ← mapMat_mapMat_adj B.data B.off B.ld (Nat.zero_le j) (by lia : j ≤ j + 4), ← hinv]
  apply mapMat_congr
  intro i c v hi h₁ h₂
  have hc : B.off + B.ld * c + m ≤ (mapMat b B.off B.ld m j (j + 4) fun _ _ v => α * v).size := by
    have := Nat.mul_le_mul_left B.ld (show c ≤ j + 3 by lia)
    rw [size_mapMat, hb]; lia
  simp only [lowerColAt, dite_eq_left hc, lowerAt, ite_eq_left hi]
  unfold trsmColAt
  apply trsvLower_congr d A _ i hi
  intro l hl
  have hp : B.off + B.ld * c + l < b.size := by rw [size_mapMat] at hc; lia
  simp only [colAt, Nat.one_mul]
  rw [getElem!_mapMat_col b B.off B.ld j (j + 4) _ B.le_ld ⟨h₁, h₂⟩ hl hp, hinv,
    getElem!_mapMat_col_of_not _ _ _ _ _ _ B.le_ld (by lia) hl,
    getElem!_index (Vec.ofFn fun l : Fin m => α * B.data[B.off + B.ld * c + l.val]!) hl,
    Vec.getElem_ofFn]

/--
Four columns of `trsmLoop` on the upper triangle map the columns `j` to `j + 3` to their solutions.
-/
private theorem trsmUpper4_step (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (j : Nat)
    (hq : B.off + B.ld * (j + 3) + m ≤ B.data.size)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (b : Float64Array)
    (hb : b.size = B.data.size)
    (hinv : b = mapMat B.data B.off B.ld m 0 j (trsmColAt .upper d α A B B.data)) :
    trsmUpper4Data d α A B.off B.ld b j (hb ▸ hq) (hb ▸ hs) =
      mapMat B.data B.off B.ld m 0 (j + 4) (trsmColAt .upper d α A B B.data) := by
  rw [trsmUpper4Data_eq _ _ _ _ _ B.le_ld, mapMat_mapMat,
    ← mapMat_mapMat_adj B.data B.off B.ld (Nat.zero_le j) (by lia : j ≤ j + 4), ← hinv]
  apply mapMat_congr
  intro i c v hi h₁ h₂
  have hc : B.off + B.ld * c + m ≤ (mapMat b B.off B.ld m j (j + 4) fun _ _ v => α * v).size := by
    have := Nat.mul_le_mul_left B.ld (show c ≤ j + 3 by lia)
    rw [size_mapMat, hb]; lia
  simp only [upperColAt, dite_eq_left hc, upperAt, ite_eq_left (show m - m ≤ i by lia)]
  unfold trsmColAt
  apply trsvUpper_congr d A _ i hi
  intro l hl
  have hp : B.off + B.ld * c + l < b.size := by rw [size_mapMat] at hc; lia
  simp only [colAt, Nat.one_mul]
  rw [getElem!_mapMat_col b B.off B.ld j (j + 4) _ B.le_ld ⟨h₁, h₂⟩ hl hp, hinv,
    getElem!_mapMat_col_of_not _ _ _ _ _ _ B.le_ld (by lia) hl,
    getElem!_index (Vec.ofFn fun l : Fin m => α * B.data[B.off + B.ld * c + l.val]!) hl,
    Vec.getElem_ofFn]

/-- `trsmLoop` from column `j`, after the columns before `j` are solved, solves all of them. -/
private theorem trsmLoop_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j ≤ n) (b : Float64Array) (hb : b.size = B.data.size)
    (hinv : b = mapMat B.data B.off B.ld m 0 j (trsmColAt uplo d α A B B.data)) :
    trsmLoop uplo d α A B.off B.ld B.data.size B.le_ld B.bound j b hb =
      mapMat B.data B.off B.ld m 0 n (trsmColAt uplo d α A B B.data) := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing j b with
  | ind e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | he0
    · obtain rfl : j = n := by lia
      rw [trsmLoop, dite_eq_right (Nat.lt_irrefl _), hinv]
    have hjn : j < n := by lia
    rw [trsmLoop, dite_eq_left hjn]
    split
    · rename_i h4
      obtain ⟨h4, hm, hs⟩ := h4
      refine ih (n - (j + 4)) (by lia) (j + 4) h4 _ _ ?_ rfl
      cases uplo
      · exact trsmUpper4_step d α A B j (cols4_le B.bound rfl h4 hm) hs b hb hinv
      · exact trsmLower4_step d α A B j (cols4_le B.bound rfl h4 hm) hs b hb hinv
    · refine ih (n - (j + 1)) (by lia) (j + 1) hjn _ _ ?_ rfl
      have hcol : ∀ l, l < m → b[B.off + B.ld * j + l]! = B.data[B.off + B.ld * j + l]! := by
        intro l hl
        rw [hinv, getElem!_mapMat_col_of_not _ _ _ _ _ _ B.le_ld (by lia) hl]
      rw [trsmLoop_step uplo d α A B j hjn b hb B.data hcol, hinv]
      exact modifyAt_col_mapMat _ _ _ B.le_ld j _

/-- The array of `trsm`. -/
public def trsmData (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Float64Array :=
  if α == 0 then B.scalBetaData 0
  else trsmLoop uplo d α A B.off B.ld B.data.size B.le_ld B.bound 0 B.data rfl

public theorem trsmData_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    trsmData uplo d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmAt uplo d α A B i j := by
  unfold trsmData
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [trsmLoop_eq uplo d α A B 0 (Nat.zero_le _) _ rfl
      (mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)).symm]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmColAt, trsmAt, scaledCol, hα]
  · simp only [↓reduceIte, scalBetaData_eq]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmAt, betaMul, hα, show ((0 : Float) == 0) = true from rfl]

/--
`trsm uplo d α A B` solves `A * X = α * B` for the triangle `uplo` of `A`, with a unit diagonal if
`d` is `.unit`, over `B`, by the loops of the reference BLAS: for each column `j` of `B`, it scales
the column by `α`, then solves it by the loops of `trsv`. It solves four columns at a time, which
share the reads of `A`, with the same operations on each element. It updates `B` in place when its
array is not shared, and leaves the elements of the array outside `B` unchanged. As in the
reference BLAS, it sets `B` to `0` without reading `A` or `B` when `α = 0`, reads only the triangle
`uplo` of `A`, and not its diagonal when `d` is `.unit`, and doesn't check for a zero on the
diagonal.
-/
@[expose] public def trsm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Mat m n where
  data := trsmData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trsmData_eq, size_mapMat]; exact B.bound

/-- The array of `trsm uplo d α A B` is the array of `B` with its elements solved. -/
public theorem data_trsm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    (trsm uplo d α A B).data =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmAt uplo d α A B i j :=
  trsmData_eq uplo d α A B

@[simp] public theorem off_trsm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (B : Mat m n) : (trsm uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trsm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (B : Mat m n) : (trsm uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trsm uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trsm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) : (trsm uplo d α A B)[(i, j)] = trsmAt uplo d α A B i j :=
  getElem_of_data_eq_mapMat _ (data_trsm uplo d α A B) rfl rfl i j h

/--
Element `(i, j)` of `X = trsm .lower d α A B` is `0` when `α = 0`, and otherwise `α * B[i, j]`,
minus the terms `X[l, j] * A[i, l]` for `l = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal
is unit: forward substitution, in the order of the loops.
-/
public theorem getElem_trsm_lower (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trsm .lower d α A B)[(i, j)] =
      if α == 0 then 0
      else d.apply (Nat.fold i (fun l hl s =>
          s - (trsm .lower d α A B)[(l, j)]'⟨by lia, h.2⟩ * A[(i, l)]'⟨h.1, by lia⟩)
        (α * B[(i, j)])) A[(i, i)] := by
  rw [getElem_trsm _ _ _ _ _ _ _ h, trsmAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trsvSol]
    rw [trsvLower_eq d A _ h.1]
    congr 1
    · congr 1
      · funext l hl s
        rw [getElem_trsm _ _ _ _ _ _ _ ⟨by lia, h.2⟩, trsmAt, hα]
        rfl
      · simp only [scaledCol, Vec.getElem_ofFn, getElem_def]
        rw [getElem!_pos B.data _ (B.index_lt h.1 h.2)]
  · rfl

/--
Element `(i, j)` of `X = trsm .upper d α A B` is `0` when `α = 0`, and otherwise `α * B[i, j]`,
minus the terms `X[l, j] * A[i, l]` for `l = m - 1, …, i + 1`, divided by `A[i, i]` unless the
diagonal is unit: back substitution, in the order of the loops.
-/
public theorem getElem_trsm_upper (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trsm .upper d α A B)[(i, j)] =
      if α == 0 then 0
      else d.apply (Nat.fold (m - 1 - i) (fun t _ s =>
          s - (trsm .upper d α A B)[(m - 1 - t, j)]'⟨by lia, h.2⟩ * A[(i, m - 1 - t)]'⟨h.1, by lia⟩)
        (α * B[(i, j)])) A[(i, i)] := by
  rw [getElem_trsm _ _ _ _ _ _ _ h, trsmAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trsvSol]
    rw [trsvUpper_eq d A _ h.1]
    congr 1
    · congr 1
      · funext t ht s
        rw [getElem_trsm _ _ _ _ _ _ _ ⟨by lia, h.2⟩, trsmAt, hα]
        rfl
      · simp only [scaledCol, Vec.getElem_ofFn, getElem_def]
        rw [getElem!_pos B.data _ (B.index_lt h.1 h.2)]
  · rfl

/-! ## `trsmRight` -/

/--
Element `(i, j)` of the solution of `X * A = α * B` for the upper triangle of `A`, on the arrays:
`α * B[i, j]`, minus the terms `A[k, j] * X[i, k]` for `k = 0, …, j - 1`, divided by `A[j, j]`
unless the diagonal is unit.
-/
public def trsmRightUpper (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat) :
    Float :=
  d.apply (Nat.fold j (fun k _hk s =>
      s - A.data[A.off + A.ld * j + k]! * trsmRightUpper d α A B i k)
    (α * B.data[B.off + B.ld * j + i]!)) A.data[A.off + A.ld * j + j]!
termination_by j
decreasing_by exact _hk

/--
Element `(i, j)` of the solution of `X * A = α * B` for the lower triangle of `A`, on the arrays:
`α * B[i, j]`, minus the terms `A[k, j] * X[i, k]` for `k = j + 1, …, n - 1`, divided by `A[j, j]`
unless the diagonal is unit.
-/
public def trsmRightLower (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat) :
    Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (j + 1 + t)]! * trsmRightLower d α A B i (j + 1 + t))
    (α * B.data[B.off + B.ld * j + i]!)) A.data[A.off + A.ld * j + j]!
termination_by n - j
decreasing_by lia

/-- Dividing the rows `0 ≤ i < d.rows m` by `t` is `Diag.apply` on all of them. -/
private theorem modifyAt_rows (b : Float64Array) (idx : Nat → Nat) (d : Diag) {mu : USize}
    (hmu : mu.toNat = m) (t : Float) :
    b.modifyAt idx 0 (d.rows mu).toNat (fun _ v => v / t) =
      b.modifyAt idx 0 m fun _ v => d.apply v t := by
  cases d
  · simp only [Diag.rows, USize.toNat_zero, modifyAt_self, Diag.apply]
    rw [modifyAt_id]
  · simp only [Diag.rows, hmu, Diag.apply]

/--
Subtracting `w k` times column `k` of `c` from column `j`, for the columns `k` from `lo` to
`lo + K - 1`, which are not column `j`, subtracts the terms in that order from each element.
-/
private theorem iterRange_subCols (c : Float64Array) (oj : Nat) (ok : Nat → Nat) (w : Nat → Float)
    (lo K : Nat) (hd : ∀ k, lo ≤ k → k < lo + K → ∀ i, i < m → ∀ i', i' < m → oj + i ≠ ok k + i') :
    iterRange (fun k c => c.modifyAt (Stride.mk oj 1).idx 0 m fun i v => v - w k * c[ok k + i]!)
        lo (lo + K) c =
      c.modifyAt (Stride.mk oj 1).idx 0 m fun i v =>
        Nat.fold K (fun t _ s => s - w (lo + t) * c[ok (lo + t) + i]!) v := by
  induction K with
  | zero =>
    rw [Nat.add_zero, iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _; rw [Nat.fold_zero]
  | succ K ih =>
    rw [← Nat.add_assoc, iterRange_succ _ (Nat.le_add_right _ _),
      ih (fun k h₁ h₂ => hd k h₁ (by lia)), modifyAt_modifyAt _ _ (col_injOn _ _ _)]
    apply modifyAt_congr_fun
    intro i v _ hi
    rw [Nat.fold_succ, getElem!_modifyAt_of_ne _ _ _ (fun i' _ hi' e => by
      simp only [Stride.idx, Nat.one_mul] at e
      exact hd (lo + K) (Nat.le_add_right _ _) (by lia) i' hi' i hi e)]

/-- The array of `trsmRight .upper`, for `α ≠ 0`. -/
public def trsmRightUpperData (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let b := B.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    (inplace b do
      for j in 0...nu do
        let cj := bo + bl * j
        for i in 0...mu do
          have hk : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
          b[cj + 1 * i] := α * b[cj + 1 * i]
        for k in 0...j do
          let t := A.uget ao al rfl rfl hs.1 k j (by lia) (by lia)
          let ck := bo + bl * k
          for i in 0...mu do
            have hk : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
            have hk' : (ck + 1 * i).toNat < b.size :=
              B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
            b[cj + 1 * i] := b[cj + 1 * i] - t * b[ck + 1 * i]
        let ajj := A.uget ao al rfl rfl hs.1 j j (by lia) (by lia)
        -- A unit diagonal runs an empty loop: an `if` would allocate a closure per column.
        for i in 0...d.rows mu do
          have hk : (cj + 1 * i).toNat < b.size :=
            B.toNat_col_index_lt hs.2.1 (Nat.lt_of_lt_of_le (by assumption)
              (hmu ▸ d.toNat_rows_le)) (by lia)
          b[cj + 1 * i] := b[cj + 1 * i] / ajj).2
  else mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightUpper d α A B i j

/--
The value of column `j` of `trsmRight .upper` from its old value `v`, with the columns before it.
-/
private def trsmRightUpperG (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat)
    (v : Float) : Float :=
  d.apply (Nat.fold j (fun k _ s => s - A.data[A.off + A.ld * j + k]! * trsmRightUpper d α A B i k)
    (α * v)) A.data[A.off + A.ld * j + j]!

private theorem trsmRightUpper_eq_G (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    (i j : Nat) :
    trsmRightUpper d α A B i j = trsmRightUpperG d α A B i j B.data[B.off + B.ld * j + i]! := by
  rw [trsmRightUpper]; rfl

/-- The step of `trsmRight .upper` for column `j`, on the array `c`. -/
private def trsmRightUpperCol (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (j : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt (Stride.mk (B.off + B.ld * j) 1).idx 0 m fun i v =>
    d.apply (Nat.fold j (fun k _ s => s - A.data[A.off + A.ld * j + k]! * c[B.off + B.ld * k + i]!)
      (α * v)) A.data[A.off + A.ld * j + j]!

private theorem iterRange_trsmRightUpperCol (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    {J : Nat} (hJ : J ≤ n) :
    iterRange (trsmRightUpperCol d α A B) 0 J B.data =
      mapMat B.data B.off B.ld m 0 J (trsmRightUpperG d α A B) := by
  induction J with
  | zero => rw [iterRange_self, mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ J ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), trsmRightUpperCol,
      ← modifyAt_col_mapMat _ _ _ B.le_ld J]
    apply modifyAt_congr_fun
    intro i v _ hi
    simp only [trsmRightUpperG]
    congr 2
    funext k hk s
    rw [getElem!_mapMat_col _ _ _ _ _ _ B.le_ld ⟨Nat.zero_le _, hk⟩ hi (B.index_lt hi (by lia)),
      ← trsmRightUpper_eq_G]

public theorem trsmRightUpperData_eq (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) :
    trsmRightUpperData d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightUpper d α A B i j := by
  unfold trsmRightUpperData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsmRightUpperCol d α A B)
      (hF := by simp [trsmRightUpperCol])]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_trsmRightUpperCol d α A B (Nat.le_refl _)]
      apply mapMat_congr_getElem
      intro i j hi _ hj hq
      rw [trsmRightUpper_eq_G, getElem!_pos B.data _ hq]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hcol : ∀ k, k ≠ j.toNat → ∀ i, i < m → ∀ i', i' < m →
          B.off + B.ld * j.toNat + i ≠ B.off + B.ld * k + i' :=
        fun k hk i hi i' hi' => col_index_ne hi hi' B.le_ld (Ne.symm hk)
      rw [Tail.run_forInFrom_modify (G := fun _ v => α * v)
        (idx := (Stride.mk (B.off + B.ld * j.toNat) 1).idx)
        (he := fun i _ hi => B.toNat_col_index hs.2.1 (by rw [hmu] at hi; exact hi) hj)]
      · rw [Tail.run_forInFrom_unit (F := fun k c =>
          c.modifyAt (Stride.mk (B.off + B.ld * j.toNat) 1).idx 0 m fun i v =>
            v - A.data[A.off + A.ld * j.toNat + k]! * c[B.off + B.ld * k + i]!)
          (hF := by simp)]
        · rw [Tail.run_forInFrom_modify
            (G := fun _ v => v / A.data[A.off + A.ld * j.toNat + j.toNat]!)
            (idx := (Stride.mk (B.off + B.ld * j.toNat) 1).idx)
            (he := fun i _ hi => B.toNat_col_index hs.2.1
              (by have := d.toNat_rows_le (mu := m.toUSize); lia) hj)]
          · apply run_congr
            have hsub := iterRange_subCols (m := m)
              (a.modifyAt (Stride.mk (B.off + B.ld * j.toNat) 1).idx 0 m fun _ v => α * v)
              (B.off + B.ld * j.toNat) (fun k => B.off + B.ld * k)
              (fun k => A.data[A.off + A.ld * j.toNat + k]!) 0 j.toNat
              (fun k _ hk i hi i' hi' => hcol k (by lia) i hi i' hi')
            simp only [Nat.zero_add] at hsub
            rw [USize.toNat_zero, hmu, hsub, modifyAt_rows _ _ d hmu,
              modifyAt_modifyAt _ _ (col_injOn _ _ _), modifyAt_modifyAt _ _ (col_injOn _ _ _),
              trsmRightUpperCol]
            apply modifyAt_congr_fun
            intro i v _ hi
            congr 2
            funext k hk s
            rw [getElem!_modifyAt_of_ne _ _ _ (fun i' _ hi' e => by
              simp only [Stride.idx, Nat.one_mul] at e
              exact hcol k (by lia) i' hi' i hi e)]
          · intro _ _ _ _
            rw [Mat.uget_eq_getElem, getElem_def,
              getElem!_pos A.data _ (A.index_lt hj hj)]
        · intro k _ hk next' a' h'
          have hkj : k.toNat < j.toNat := hk
          rw [Tail.run_forInFrom_unit (F := fun i c =>
              c.set! ((Stride.mk (B.off + B.ld * j.toNat) 1).idx i)
                (c[(Stride.mk (B.off + B.ld * j.toNat) 1).idx i]! -
                  A.data[A.off + A.ld * j.toNat + k.toNat]! *
                  c[(Stride.mk (B.off + B.ld * k.toNat) 1).idx i]!))
              (hF := by simp)]
          · apply run_congr
            rw [USize.toNat_zero, hmu,
              iterRange_set!_read _ _ _
                (fun i v w => v - A.data[A.off + A.ld * j.toNat + k.toNat]! * w)
                (fun i _ hi i' _ hi' e => by
                  simp only [Stride.idx, Nat.one_mul] at e
                  exact hcol k.toNat (by lia) i hi i' hi' e)]
            apply modifyAt_congr_fun
            intro i v _ _
            simp only [Stride.idx, Nat.one_mul]
          · intro i _ hi next'' a'' h''
            rw [hmu] at hi
            simp only [Tail.run_readThen, Tail.run_writeThen]
            apply run_set_eq_set!
            · exact B.toNat_col_index hs.2.1 hi hj
            · have h1 := B.toNat_col_index hs.2.1 hi hj
              have h2 := B.toNat_col_index hs.2.1 hi (Nat.lt_trans hkj hj)
              simp only [Mat.uget_eq_getElem, getElem_def, h1, h2, Stride.idx, Nat.one_mul]
              rw [getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hj),
                getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi (Nat.lt_trans hkj hj)),
                getElem!_pos A.data _ (A.index_lt (Nat.lt_trans hkj hj) hj)]
      · intro _ _ _ _; rfl
  · rfl

/-- The array of `trsmRight .lower`, for `α ≠ 0`. -/
public def trsmRightLowerData (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let b := B.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    (inplace b do
      for t in 0...nu do
        let j := nu - 1 - t
        have hj : j.toNat = n - 1 - t.toNat := by grind
        have hjn : j.toNat < n := by lia
        have hj1 : (j + 1).toNat = j.toNat + 1 := by grind
        let cj := bo + bl * j
        for i in 0...mu do
          have hk : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hjn
          b[cj + 1 * i] := α * b[cj + 1 * i]
        for k in (j + 1)...nu do
          let w := A.uget ao al rfl rfl hs.1 k j (by lia) hjn
          let ck := bo + bl * k
          for i in 0...mu do
            have hk : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hjn
            have hk' : (ck + 1 * i).toNat < b.size :=
              B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
            b[cj + 1 * i] := b[cj + 1 * i] - w * b[ck + 1 * i]
        let ajj := A.uget ao al rfl rfl hs.1 j j hjn hjn
        for i in 0...d.rows mu do
          have hk : (cj + 1 * i).toNat < b.size :=
            B.toNat_col_index_lt hs.2.1 (Nat.lt_of_lt_of_le (by assumption)
              (hmu ▸ d.toNat_rows_le)) hjn
          b[cj + 1 * i] := b[cj + 1 * i] / ajj).2
  else mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightLower d α A B i j

/--
The value of column `j` of `trsmRight .lower` from its old value `v`, with the columns after it.
-/
private def trsmRightLowerG (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat)
    (v : Float) : Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (j + 1 + t)]! * trsmRightLower d α A B i (j + 1 + t))
    (α * v)) A.data[A.off + A.ld * j + j]!

private theorem trsmRightLower_eq_G (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    (i j : Nat) :
    trsmRightLower d α A B i j = trsmRightLowerG d α A B i j B.data[B.off + B.ld * j + i]! := by
  rw [trsmRightLower]; rfl

/-- The step `t` of `trsmRight .lower`, for column `j = n - 1 - t`, on the array `c`. -/
private def trsmRightLowerCol (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (t : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt (Stride.mk (B.off + B.ld * (n - 1 - t)) 1).idx 0 m fun i v =>
    d.apply (Nat.fold (n - 1 - (n - 1 - t)) (fun t' _ s =>
        s - A.data[A.off + A.ld * (n - 1 - t) + (n - 1 - t + 1 + t')]! *
          c[B.off + B.ld * (n - 1 - t + 1 + t') + i]!)
      (α * v)) A.data[A.off + A.ld * (n - 1 - t) + (n - 1 - t)]!

private theorem iterRange_trsmRightLowerCol (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    {T : Nat} (hT : T ≤ n) :
    iterRange (trsmRightLowerCol d α A B) 0 T B.data =
      mapMat B.data B.off B.ld m (n - T) n (trsmRightLowerG d α A B) := by
  induction T with
  | zero => rw [iterRange_self, Nat.sub_zero, mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ T ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), trsmRightLowerCol,
      show n - T = n - 1 - T + 1 by lia, show n - (T + 1) = n - 1 - T by lia,
      ← modifyAt_col_mapMat_lo _ _ _ B.le_ld (show n - 1 - T < n by lia)]
    apply modifyAt_congr_fun
    intro i v _ hi
    simp only [trsmRightLowerG]
    congr 2
    funext t' ht' s
    rw [getElem!_mapMat_col _ _ _ _ _ _ B.le_ld ⟨by lia, by lia⟩ hi (B.index_lt hi (by lia)),
      ← trsmRightLower_eq_G]

public theorem trsmRightLowerData_eq (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) :
    trsmRightLowerData d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightLower d α A B i j := by
  unfold trsmRightLowerData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsmRightLowerCol d α A B)
      (hF := by simp [trsmRightLowerCol])]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_trsmRightLowerCol d α A B (Nat.le_refl _), Nat.sub_self]
      apply mapMat_congr_getElem
      intro i j hi _ hj hq
      rw [trsmRightLower_eq_G, getElem!_pos B.data _ hq]
    · intro t _ ht next a h
      rw [hnu] at ht
      have hj : (n.toUSize - 1 - t).toNat = n - 1 - t.toNat := by grind
      have hjn : n - 1 - t.toNat < n := by lia
      have hj1 : (n.toUSize - 1 - t + 1).toNat = n - 1 - t.toNat + 1 := by grind
      have hcol : ∀ k, k ≠ n - 1 - t.toNat → ∀ i, i < m → ∀ i', i' < m →
          B.off + B.ld * (n - 1 - t.toNat) + i ≠ B.off + B.ld * k + i' :=
        fun k hk i hi i' hi' => col_index_ne hi hi' B.le_ld (Ne.symm hk)
      rw [Tail.run_forInFrom_modify (G := fun _ v => α * v)
        (idx := (Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx)
        (e := fun i => B.off.toUSize + B.ld.toUSize * (n.toUSize - 1 - t) + 1 * i)
        (he := fun i _ hi => by
          rw [B.toNat_col_index hs.2.1 (by rw [hmu] at hi; exact hi) (by rw [hj]; exact hjn), hj]
          rfl)]
      · rw [Tail.run_forInFrom_unit (F := fun k c =>
          c.modifyAt (Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx 0 m fun i v =>
            v - A.data[A.off + A.ld * (n - 1 - t.toNat) + k]! * c[B.off + B.ld * k + i]!)
          (hF := by simp)]
        · rw [Tail.run_forInFrom_modify
            (G := fun _ v => v / A.data[A.off + A.ld * (n - 1 - t.toNat) + (n - 1 - t.toNat)]!)
            (idx := (Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx)
            (e := fun i => B.off.toUSize + B.ld.toUSize * (n.toUSize - 1 - t) + 1 * i)
            (he := fun i _ hi => by
              rw [B.toNat_col_index hs.2.1 (by have := d.toNat_rows_le (mu := m.toUSize); lia)
                (by rw [hj]; exact hjn), hj]
              rfl)]
          · apply run_congr
            have hsub := iterRange_subCols (m := m)
              (a.modifyAt (Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx 0 m fun _ v => α * v)
              (B.off + B.ld * (n - 1 - t.toNat)) (fun k => B.off + B.ld * k)
              (fun k => A.data[A.off + A.ld * (n - 1 - t.toNat) + k]!) (n - 1 - t.toNat + 1)
              (n - 1 - (n - 1 - t.toNat))
              (fun k hk _ i hi i' hi' => hcol k (by lia) i hi i' hi')
            rw [show n - 1 - t.toNat + 1 + (n - 1 - (n - 1 - t.toNat)) = n by lia] at hsub
            rw [hj1, hnu, USize.toNat_zero, hmu, hsub, modifyAt_rows _ _ d hmu,
              modifyAt_modifyAt _ _ (col_injOn _ _ _), modifyAt_modifyAt _ _ (col_injOn _ _ _),
              trsmRightLowerCol]
            apply modifyAt_congr_fun
            intro i v _ hi
            congr 2
            funext k hk s
            rw [getElem!_modifyAt_of_ne _ _ _ (fun i' _ hi' e => by
              simp only [Stride.idx, Nat.one_mul] at e
              exact hcol _ (by lia) i' hi' i hi e)]
          · intro _ _ _ _
            rw [Mat.uget_eq_getElem, getElem_def]
            simp only [hj]
            rw [getElem!_pos A.data _ (A.index_lt hjn hjn)]
        · intro k hk₁ hk next' a' h'
          rw [hnu] at hk
          rw [hj1] at hk₁
          have hkn : k.toNat < n := hk
          rw [Tail.run_forInFrom_unit (F := fun i c =>
              c.set! ((Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx i)
                (c[(Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx i]! -
                  A.data[A.off + A.ld * (n - 1 - t.toNat) + k.toNat]! *
                  c[(Stride.mk (B.off + B.ld * k.toNat) 1).idx i]!))
              (hF := by simp)]
          · apply run_congr
            rw [USize.toNat_zero, hmu,
              iterRange_set!_read _ _ _
                (fun i v w => v - A.data[A.off + A.ld * (n - 1 - t.toNat) + k.toNat]! * w)
                (fun i _ hi i' _ hi' e => by
                  simp only [Stride.idx, Nat.one_mul] at e
                  exact hcol k.toNat (by lia) i hi i' hi' e)]
            apply modifyAt_congr_fun
            intro i v _ _
            simp only [Stride.idx, Nat.one_mul]
          · intro i _ hi next'' a'' h''
            rw [hmu] at hi
            simp only [Tail.run_readThen, Tail.run_writeThen]
            apply run_set_eq_set!
            · rw [B.toNat_col_index hs.2.1 hi (by rw [hj]; exact hjn), hj]
              rfl
            · have h1 :=
                B.toNat_col_index hs.2.1 hi (j := n.toUSize - 1 - t) (by rw [hj]; exact hjn)
              have h2 := B.toNat_col_index hs.2.1 hi hkn
              simp only [Mat.uget_eq_getElem, getElem_def, h1, h2, hj, Stride.idx, Nat.one_mul]
              rw [getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hjn),
                getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hkn),
                getElem!_pos A.data _ (A.index_lt hkn hjn)]
      · intro _ _ _ _; rfl
  · rfl

/-- The solution of `X * A = α * B` for the triangle `uplo` of `A`, element by element. -/
@[expose] public def trsmRightSol (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) : Nat → Nat → Float :=
  match uplo with
  | .upper => trsmRightUpper d α A B
  | .lower => trsmRightLower d α A B

/-- The value of `trsmRight` at `(i, j)`: `0` when `α = 0`, and the solution otherwise. -/
@[expose] public def trsmRightAt (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    (i j : Nat) : Float :=
  if α == 0 then 0 else trsmRightSol uplo d α A B i j

/-- The array of `trsmRight`. -/
public def trsmRightData (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) :
    Float64Array :=
  if α == 0 then B.scalBetaData 0
  else
    match uplo with
    | .upper => trsmRightUpperData d α A B
    | .lower => trsmRightLowerData d α A B

public theorem trsmRightData_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) :
    trsmRightData uplo d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightAt uplo d α A B i j := by
  unfold trsmRightData
  cases hα : α == 0
  · cases uplo
    · simp only [Bool.false_eq_true, ↓reduceIte, trsmRightUpperData_eq]
      apply mapMat_congr
      intro i j v _ _ _
      simp [trsmRightAt, trsmRightSol, hα]
    · simp only [Bool.false_eq_true, ↓reduceIte, trsmRightLowerData_eq]
      apply mapMat_congr
      intro i j v _ _ _
      simp [trsmRightAt, trsmRightSol, hα]
  · simp only [↓reduceIte, scalBetaData_eq]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmRightAt, betaMul, hα, show ((0 : Float) == 0) = true from rfl]

/--
`trsmRight uplo d α A B` solves `X * A = α * B` for the triangle `uplo` of `A`, with a unit
diagonal if `d` is `.unit`, over `B`, by the loops of the reference BLAS: for the upper triangle,
for each column `j` of `B` from `0` to `n - 1`, it scales the column by `α`, subtracts `A[k, j]`
times column `k` for `k = 0, …, j - 1`, and divides it by `A[j, j]` unless the diagonal is unit;
for the lower triangle, it does the same from `j = n - 1` down to `0`, with `k = j + 1, …, n - 1`.
It updates `B` in place when its array is not shared, and leaves the elements of the array outside
`B` unchanged. As in the reference BLAS, it sets `B` to `0` without reading `A` or `B` when
`α = 0`, reads only the triangle `uplo` of `A`, and doesn't check for a zero on the diagonal.
-/
@[expose] public def trsmRight (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) :
    Mat m n where
  data := trsmRightData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trsmRightData_eq, size_mapMat]; exact B.bound

/-- The array of `trsmRight uplo d α A B` is the array of `B` with its elements solved. -/
public theorem data_trsmRight (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) :
    (trsmRight uplo d α A B).data =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightAt uplo d α A B i j :=
  trsmRightData_eq uplo d α A B

@[simp] public theorem off_trsmRight (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) : (trsmRight uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trsmRight (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) : (trsmRight uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trsmRight uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trsmRight (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRight uplo d α A B)[(i, j)] = trsmRightAt uplo d α A B i j :=
  getElem_of_data_eq_mapMat _ (data_trsmRight uplo d α A B) rfl rfl i j h

/--
Element `(i, j)` of `X = trsmRight .upper d α A B` is `0` when `α = 0`, and otherwise
`α * B[i, j]`, minus the terms `A[k, j] * X[i, k]` for `k = 0, …, j - 1`, divided by `A[j, j]`
unless the diagonal is unit, in the order of the loops.
-/
public theorem getElem_trsmRight_upper (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRight .upper d α A B)[(i, j)] =
      if α == 0 then 0
      else d.apply (Nat.fold j (fun k hk s =>
          s - A[(k, j)]'⟨by lia, h.2⟩ * (trsmRight .upper d α A B)[(i, k)]'⟨h.1, by lia⟩)
        (α * B[(i, j)])) A[(j, j)] := by
  rw [getElem_trsmRight _ _ _ _ _ _ _ h, trsmRightAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trsmRightSol]
    rw [trsmRightUpper, getElem!_pos B.data _ (B.index_lt h.1 h.2),
      getElem!_pos A.data _ (A.index_lt h.2 h.2)]
    congr 2
    funext k hk s
    rw [getElem_trsmRight _ _ _ _ _ _ _ ⟨h.1, by lia⟩, trsmRightAt, hα,
      getElem!_pos A.data _ (A.index_lt (by lia) h.2)]
    rfl
  · rfl

/--
Element `(i, j)` of `X = trsmRight .lower d α A B` is `0` when `α = 0`, and otherwise
`α * B[i, j]`, minus the terms `A[k, j] * X[i, k]` for `k = j + 1, …, n - 1`, divided by `A[j, j]`
unless the diagonal is unit, in the order of the loops.
-/
public theorem getElem_trsmRight_lower (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRight .lower d α A B)[(i, j)] =
      if α == 0 then 0
      else d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
          s - A[(j + 1 + t, j)]'⟨by lia, h.2⟩ *
            (trsmRight .lower d α A B)[(i, j + 1 + t)]'⟨h.1, by lia⟩)
        (α * B[(i, j)])) A[(j, j)] := by
  rw [getElem_trsmRight _ _ _ _ _ _ _ h, trsmRightAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trsmRightSol]
    rw [trsmRightLower, getElem!_pos B.data _ (B.index_lt h.1 h.2),
      getElem!_pos A.data _ (A.index_lt h.2 h.2)]
    congr 2
    funext t ht s
    rw [getElem_trsmRight _ _ _ _ _ _ _ ⟨h.1, by lia⟩, trsmRightAt, hα,
      getElem!_pos A.data _ (A.index_lt (by lia) h.2)]
    rfl
  · rfl

end Mat

end BLAS.Float64
