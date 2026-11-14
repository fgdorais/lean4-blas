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
specification is that of `trsv` on the scaled column. `trsmRight` updates column `j` of `B` with the
columns already solved, and its specification is the recursive model `trsmRightUpper` or
`trsmRightLower`.
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

/-- An element of a column `j` of a `mapMat` is mapped. -/
private theorem getElem!_mapMat_col (a : Float64Array) (off ld lo hi : Nat)
    (g : Nat → Nat → Float → Float) (hml : m ≤ ld) {j : Nat} (hj : lo ≤ j ∧ j < hi) {l : Nat}
    (hl : l < m) (hq : off + ld * j + l < a.size) :
    (mapMat a off ld m lo hi g)[off + ld * j + l]! = g l j a[off + ld * j + l]! := by
  rw [getElem!_pos _ _ (by rw [size_mapMat]; exact hq), getElem!_pos a _ hq,
    getElem_mapMat_index _ _ _ _ _ _ _ hl hml hj hq]

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

/--
The loop of `trsm` over the columns from `j`, on the array `b` of an `m × n` matrix: it scales
column `j` by `α`, then solves it by `trsv`. It takes the offset and the leading dimension of the
matrix rather than the matrix, which would keep a second reference to its array.
-/
public def trsmLoop (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (j : Nat) (b : Float64Array)
    (hb : b.size = sz) : Float64Array :=
  if hj : j < n then
    trsmLoop uplo d α A off ld sz hsz (j + 1)
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

/-- `trsmLoop` from column `j`, after the columns before `j` are solved, solves all of them. -/
private theorem trsmLoop_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j ≤ n) (b : Float64Array) (hb : b.size = B.data.size)
    (hinv : b = mapMat B.data B.off B.ld m 0 j (trsmColAt uplo d α A B B.data)) :
    trsmLoop uplo d α A B.off B.ld B.data.size B.bound j b hb = mapMat B.data B.off B.ld m 0 n (trsmColAt uplo d α A B B.data) := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e generalizing j b with
  | zero =>
    obtain rfl : j = n := by lia
    rw [trsmLoop, dite_eq_right (Nat.lt_irrefl _), hinv]
  | succ e ih =>
    have hjn : j < n := by lia
    rw [trsmLoop, dite_eq_left hjn]
    refine ih (j + 1) hjn _ _ ?_ (by lia)
    have hcol : ∀ l, l < m → b[B.off + B.ld * j + l]! = B.data[B.off + B.ld * j + l]! := by
      intro l hl
      rw [hinv, getElem!_mapMat_col_of_not _ _ _ _ _ _ B.le_ld (by lia) hl]
    rw [trsmLoop_step uplo d α A B j hjn b hb B.data hcol, hinv]
    exact modifyAt_col_mapMat _ _ _ B.le_ld j _

/-- The array of `trsm`. -/
public def trsmData (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Float64Array :=
  if α == 0 then B.scalBetaData 0 else trsmLoop uplo d α A B.off B.ld B.data.size B.bound 0 B.data rfl

public theorem trsmData_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    trsmData uplo d α A B = mapMat B.data B.off B.ld m 0 n fun i j _ => trsmAt uplo d α A B i j := by
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
the column by `α`, then solves it by the loops of `trsv`. It updates `B` in place when its array is
not shared, and leaves the elements of the array outside `B` unchanged. As in the reference BLAS, it
sets `B` to `0` without reading `A` or `B` when `α = 0`, reads only the triangle `uplo` of `A`,
and not its diagonal when `d` is `.unit`, and doesn't check for a zero on the diagonal.
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
public def trsmRightUpper (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat) : Float :=
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
public def trsmRightLower (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat) : Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (j + 1 + t)]! * trsmRightLower d α A B i (j + 1 + t))
    (α * B.data[B.off + B.ld * j + i]!)) A.data[A.off + A.ld * j + j]!
termination_by n - j
decreasing_by lia

/-- Dividing the rows `0 ≤ i < d.rows m` by `t` is `Diag.apply` on all of them. -/
private theorem modifyAt_rows (b : Float64Array) (idx : Nat → Nat) (d : Diag) {mu : USize}
    (hmu : mu.toNat = m) (t : Float) :
    b.modifyAt idx 0 (d.rows mu).toNat (fun _ v => v / t) = b.modifyAt idx 0 m fun _ v => d.apply v t := by
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

/-- The value of column `j` of `trsmRight .upper` from its old value `v`, with the columns before it. -/
private def trsmRightUpperG (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat)
    (v : Float) : Float :=
  d.apply (Nat.fold j (fun k _ s => s - A.data[A.off + A.ld * j + k]! * trsmRightUpper d α A B i k)
    (α * v)) A.data[A.off + A.ld * j + j]!

private theorem trsmRightUpper_eq_G (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat) :
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
              iterRange_set!_read _ _ _ (fun i v w => v - A.data[A.off + A.ld * j.toNat + k.toNat]! * w)
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

/-- The value of column `j` of `trsmRight .lower` from its old value `v`, with the columns after it. -/
private def trsmRightLowerG (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat)
    (v : Float) : Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (j + 1 + t)]! * trsmRightLower d α A B i (j + 1 + t))
    (α * v)) A.data[A.off + A.ld * j + j]!

private theorem trsmRightLower_eq_G (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) (i j : Nat) :
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
            · have h1 := B.toNat_col_index hs.2.1 hi (j := n.toUSize - 1 - t) (by rw [hj]; exact hjn)
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
