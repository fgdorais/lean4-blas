/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Level1
public import BLAS.Float32.Mat
import all BLAS.Internal

/-!
# Triangular solve

`Mat.trsv uplo diag A x` solves `A * y = x` for a triangular matrix `A`, over `x`, by the
column-oriented loops of the reference BLAS. Its specification is the recursive back-substitution
model `trsvLower` or `trsvUpper`, which subtracts the terms in the order the loops do.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

/-- The triangle of a matrix that a triangular routine reads. -/
public inductive Uplo where
  /-- The elements on and above the diagonal. -/
  | upper
  /-- The elements on and below the diagonal. -/
  | lower
  deriving DecidableEq, Repr

/-- Whether a triangular routine reads the diagonal of its matrix, or takes it to be `1`. -/
public inductive Diag where
  /-- The diagonal is `1`, and the routine doesn't read it. -/
  | unit
  /-- The routine reads the diagonal. -/
  | nonUnit
  deriving DecidableEq, Repr

/-- `d.apply v a` divides `v` by the diagonal element `a`, unless the diagonal is unit. -/
@[expose] public def Diag.apply : Diag → Float32 → Float32 → Float32
  | .unit, v, _ => v
  | .nonUnit, v, a => v / a

namespace Mat

variable {n : Nat}

/-! ## The models -/

/--
Element `i` of the solution of `A * y = x` for the lower triangle of `A`, on the arrays:
`x[i]`, minus the terms `y[l] * A[i, l]` for `l = 0, …, i - 1`, divided by `A[i, i]` unless the
diagonal is unit.
-/
public def trsvLower (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat) : Float32 :=
  d.apply (Nat.fold i (fun l _hl s => s - trsvLower d A x l * A.data[A.off + A.ld * l + i]!)
    x.data[x.off + x.inc * i]!) A.data[A.off + A.ld * i + i]!
termination_by i
decreasing_by exact _hl

/--
Element `i` of the solution of `A * y = x` for the upper triangle of `A`, on the arrays:
`x[i]`, minus the terms `y[l] * A[i, l]` for `l = n - 1, …, i + 1`, divided by `A[i, i]` unless
the diagonal is unit.
-/
public def trsvUpper (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat) : Float32 :=
  d.apply (Nat.fold (n - 1 - i) (fun t _ s =>
      s - trsvUpper d A x (n - 1 - t) * A.data[A.off + A.ld * (n - 1 - t) + i]!)
    x.data[x.off + x.inc * i]!) A.data[A.off + A.ld * i + i]!
termination_by n - i
decreasing_by lia

/--
Element `i < n` of the solution of `A * y = x` for the lower triangle of `A` is `x[i]`, minus the
terms `y[l] * A[i, l]` for `l = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal is unit.
-/
public theorem trsvLower_eq (d : Diag) (A : Mat n n) (x : Vec n) {i : Nat} (h : i < n) :
    trsvLower d A x i =
      d.apply (Nat.fold i (fun l hl s => s - trsvLower d A x l * A[(i, l)]'⟨h, by lia⟩) x[i])
        A[(i, i)] := by
  rw [trsvLower, getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext l hl s
  rw [getElem!_pos A.data _ (A.index_lt h (by lia))]
  rfl

/--
Element `i < n` of the solution of `A * y = x` for the upper triangle of `A` is `x[i]`, minus the
terms `y[l] * A[i, l]` for `l = n - 1, …, i + 1`, divided by `A[i, i]` unless the diagonal is unit.
-/
public theorem trsvUpper_eq (d : Diag) (A : Mat n n) (x : Vec n) {i : Nat} (h : i < n) :
    trsvUpper d A x i =
      d.apply (Nat.fold (n - 1 - i) (fun t _ s =>
          s - trsvUpper d A x (n - 1 - t) * A[(i, n - 1 - t)]'⟨h, by lia⟩) x[i])
        A[(i, i)] := by
  rw [trsvUpper, getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos A.data _ (A.index_lt h (by lia))]
  rfl

/-! ## The lower triangle -/

/-- The step `j` of the lower solve: solve for element `j`, and update the elements below it. -/
@[expose] public def trsvLowerStep (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat)
    (b : Float32Array) : Float32Array :=
  let t := d.apply b[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!
  b.modifyAt x.stride.idx j n fun i v => if i = j then t else v - t * A.data[A.off + A.ld * j + i]!

/-
The bounds that the inner loops of the kernels below prove. `lia` can't prove them in place: its
proof would mention the loop's state, which the loop lemmas don't allow.
-/

private theorem add_one_add_lt {j k n : Nat} (h : k < n - j - 1) : j + 1 + k < n := by lia

private theorem lt_of_lt_sub_one_sub {i k n : Nat} (h : i < n - 1 - k) : i < n := by lia

/-- The array of the lower solve. -/
public def trsvLowerData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    (inplace a do
      for j in 0...nu do
        have hk : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        let v := a[o + c * j]
        let t := d.apply v (A.uget ao al rfl rfl hs.1 j j (by lia) (by lia))
        a[o + c * j] := t
        have hr : (nu - j - 1).toNat = n - j.toNat - 1 := by grind
        for k in 0...(nu - j - 1) do
          have hjk : j.toNat + 1 + k.toNat < n :=
            add_one_add_lt (by rw [← hr]; assumption)
          have hk' : (o + c * (j + 1) + c * k).toNat < a.size := by
            rw [x.toNat_index_shift hs.2 hjk]
            have := x.index_lt hjk
            rw [Nat.mul_add x.inc (j.toNat + 1), Nat.add_assoc] at *
            exact this
          a[o + c * (j + 1) + c * k] := a[o + c * (j + 1) + c * k] -
            t * A.uget ao al rfl rfl hs.1 (j + 1 + k) j
              (by
                rw [toNat_succ_add (Nat.lt_trans hjk (Nat.lt_of_le_of_lt x.le_size hs.2))]
                exact hjk) (by lia)).2
  else iterRange (trsvLowerStep d A x) 0 n x.data

public theorem trsvLowerData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvLowerData d A x = iterRange (trsvLowerStep d A x) 0 n x.data := by
  unfold trsvLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsvLowerStep d A x) (hF := by simp [trsvLowerStep])]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      simp only [Tail.run_readThen, Tail.run_writeThen]
      have hr : (n.toUSize - j - 1).toNat = n - j.toNat - 1 := by grind
      have hp : (x.off.toUSize + x.inc.toUSize * j).toNat = x.off + x.inc * j.toNat :=
        x.toNat_index hs.2 hj
      have hsz := Nat.lt_of_le_of_lt x.le_size hs.2
      rw [Tail.run_forInFrom_modify (idx := (x.stride.shift (j.toNat + 1)).idx)
        (he := fun k _ hk => x.toNat_index_shift hs.2 (by lia))
        (G := fun k v => v -
          d.apply a[x.off + x.inc * j.toNat]! A.data[A.off + A.ld * j.toNat + j.toNat]! *
          A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + k)]!)]
      · congr 1
        rw [trsvLowerStep, hr, USize.toNat_zero, set_modifyAt_succ _ x.stride _ _ hj _ hp]
        apply modifyAt_congr_fun
        intro i v h₁ h₂
        split
        · rename_i hi
          subst hi
          simp only [uget_eq_getElem, getElem_def, hp,
            getElem!_pos a (x.off + x.inc * j.toNat)
              (show _ < a.size by rw [h]; exact x.index_lt hj),
            getElem!_pos A.data (A.off + A.ld * j.toNat + j.toNat) (A.index_lt hj hj)]
        · rw [show j.toNat + 1 + (i - (j.toNat + 1)) = i by lia]
      · intro k _ hk v
        rw [hr] at hk
        simp only [uget_eq_getElem, getElem_def, hp,
          getElem!_pos a (x.off + x.inc * j.toNat) (show _ < a.size by rw [h]; exact x.index_lt hj),
          show (j + 1 + k).toNat = j.toNat + 1 + k.toNat by grind]
        rw [getElem!_pos A.data (A.off + A.ld * j.toNat + j.toNat) (A.index_lt hj hj),
          getElem!_pos A.data (A.off + A.ld * j.toNat + (j.toNat + 1 + k.toNat))
            (A.index_lt (by lia) hj)]
  · rfl

/-- After the steps `l < j`, the elements `i < j` are solved, and the others have their terms. -/
theorem iterRange_trsvLowerStep (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (hj : j ≤ n) :
    iterRange (trsvLowerStep d A x) 0 j x.data = x.data.modifyAt x.stride.idx 0 n fun i v =>
      if i < j then trsvLower d A x i
      else Nat.fold j (fun l _ s => s - trsvLower d A x l * A.data[A.off + A.ld * l + i]!) v := by
  induction j with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ j ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), trsvLowerStep]
    have ht : (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if i < j then trsvLower d A x i
          else Nat.fold j (fun l _ s => s - trsvLower d A x l * A.data[A.off + A.ld * l + i]!) v
        )[x.off + x.inc * j]! = Nat.fold j
          (fun l _ s => s - trsvLower d A x l * A.data[A.off + A.ld * l + j]!)
          x.data[x.off + x.inc * j]! := by
      rw [getElem!_pos _ (x.off + x.inc * j) (by simpa using x.index_lt (by lia : j < n)),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) (by lia),
        ite_eq_right (Nat.lt_irrefl j),
        getElem!_pos x.data (x.off + x.inc * j) (x.index_lt (by lia))]
    have ht' : d.apply (Nat.fold j
          (fun l _ s => s - trsvLower d A x l * A.data[A.off + A.ld * l + j]!)
          x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]! = trsvLower d A x j := by
      rw [trsvLower]
    simp only [ht, ht']
    rw [modifyAt_widen (lo := j) (hi := n) (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (by lia)
      (Nat.le_refl _), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : i < j
    · simp [h₁, show i < j + 1 by lia, show ¬j ≤ i by lia]
    · by_cases h₂ : i = j
      · subst h₂; simp [hi]
      · simp [h₁, h₂, show j ≤ i by lia, hi, show ¬i < j + 1 by lia, Nat.fold_succ]

/-- The array of the lower solve is the array of `x` with its elements solved. -/
public theorem trsvLowerData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvLowerData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvLower d A x i := by
  rw [trsvLowerData_eq_iterRange, iterRange_trsvLowerStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp [hi]

/-! ## The upper triangle -/

/--
The step `k` of the upper solve: solve for element `j = n - 1 - k`, and update the elements above
it.
-/
@[expose] public def trsvUpperStep (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat)
    (b : Float32Array) : Float32Array :=
  let j := n - 1 - k
  let t := d.apply b[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!
  b.modifyAt x.stride.idx 0 (j + 1) fun i v =>
    if i = j then t else v - t * A.data[A.off + A.ld * j + i]!

/-- The array of the upper solve. -/
public def trsvUpperData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    (inplace a do
      for k in 0...nu do
        have hj : (nu - 1 - k).toNat = n - 1 - k.toNat := by grind
        have hjn : (nu - 1 - k).toNat < n := by lia
        have hk : (o + c * (nu - 1 - k)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - k)]
        let t := d.apply v
          (A.uget ao al rfl rfl hs.1 (nu - 1 - k) (nu - 1 - k) hjn hjn)
        a[o + c * (nu - 1 - k)] := t
        for i in 0...(nu - 1 - k) do
          have hi : i.toNat < n := lt_of_lt_sub_one_sub (by rw [← hj]; assumption)
          have hk' : (o + c * i).toNat < a.size := x.toNat_index_lt hs.2 hi
          a[o + c * i] := a[o + c * i] -
            t * A.uget ao al rfl rfl hs.1 i (nu - 1 - k) hi hjn).2
  else iterRange (trsvUpperStep d A x) 0 n x.data

public theorem trsvUpperData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvUpperData d A x = iterRange (trsvUpperStep d A x) 0 n x.data := by
  unfold trsvUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsvUpperStep d A x) (hF := by simp [trsvUpperStep])]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro k _ hk next a h
      rw [hnu] at hk
      simp only [Tail.run_readThen, Tail.run_writeThen]
      have hj : (n.toUSize - 1 - k).toNat = n - 1 - k.toNat := by grind
      have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k)).toNat =
          x.off + x.inc * (n - 1 - k.toNat) := by
        rw [x.toNat_index hs.2 (by lia), hj]
      rw [Tail.run_forInFrom_modify (idx := x.stride.idx)
        (he := fun i _ hi => x.toNat_index hs.2 (by lia))
        (G := fun i v => v - d.apply a[x.off + x.inc * (n - 1 - k.toNat)]!
            A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat)]! *
          A.data[A.off + A.ld * (n - 1 - k.toNat) + i]!)]
      · congr 1
        rw [trsvUpperStep, hj, USize.toNat_zero,
          set_modifyAt_pred _ (s := x.stride) (N := n) (by rw [h]; exact x.fits) (by lia) _ _ _ hp]
        apply modifyAt_congr_fun
        intro i v _ _
        split
        · simp only [uget_eq_getElem, getElem_def, hp, hj,
            getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
              (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
            getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
              (A.index_lt (by lia) (by lia))]
        · rfl
      · intro i _ hi v
        rw [hj] at hi
        simp only [uget_eq_getElem, getElem_def, hp, hj,
          getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
            (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
            (A.index_lt (by lia) (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + i.toNat)
            (A.index_lt (by lia) (by lia))]
  · rfl

/--
After the steps `t < k`, the elements `i ≥ n - k` are solved, and the others have their terms.
-/
theorem iterRange_trsvUpperStep (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat} (hk : k ≤ n) :
    iterRange (trsvUpperStep d A x) 0 k x.data = x.data.modifyAt x.stride.idx 0 n fun i v =>
      if n - k ≤ i then trsvUpper d A x i
      else Nat.fold k (fun t _ s =>
        s - trsvUpper d A x (n - 1 - t) * A.data[A.off + A.ld * (n - 1 - t) + i]!) v := by
  induction k with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬n ≤ i by lia]
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), trsvUpperStep]
    have ht : (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if n - k ≤ i then trsvUpper d A x i
          else Nat.fold k (fun t _ s =>
            s - trsvUpper d A x (n - 1 - t) * A.data[A.off + A.ld * (n - 1 - t) + i]!) v
        )[x.off + x.inc * (n - 1 - k)]! = Nat.fold k (fun t _ s =>
            s - trsvUpper d A x (n - 1 - t) *
              A.data[A.off + A.ld * (n - 1 - t) + (n - 1 - k)]!)
          x.data[x.off + x.inc * (n - 1 - k)]! := by
      rw [getElem!_pos _ (x.off + x.inc * (n - 1 - k))
          (by simpa using x.index_lt (by lia : n - 1 - k < n)),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) (by lia),
        ite_eq_right (by lia),
        getElem!_pos x.data (x.off + x.inc * (n - 1 - k)) (x.index_lt (by lia))]
    have ht' : d.apply (Nat.fold k (fun t _ s =>
            s - trsvUpper d A x (n - 1 - t) *
              A.data[A.off + A.ld * (n - 1 - t) + (n - 1 - k)]!)
          x.data[x.off + x.inc * (n - 1 - k)]!)
          A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k)]! = trsvUpper d A x (n - 1 - k) := by
      rw [trsvUpper.eq_1 d A x (n - 1 - k)]
      rw [Nat.fold_congr (show n - 1 - (n - 1 - k) = k by lia)]
    simp only [ht, ht']
    rw [modifyAt_widen (lo := 0) (hi := n - 1 - k + 1) (lo' := 0) (hi' := n) _ _ _ (Nat.le_refl _)
      (Nat.zero_le _) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : n - k ≤ i
    · simp [h₁, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k + 1 by lia]
    · by_cases h₂ : i = n - 1 - k
      · subst h₂; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · simp [h₁, h₂, show ¬n - (k + 1) ≤ i by lia, show i < n - 1 - k + 1 by lia,
          Nat.fold_succ]

/-- The array of the upper solve is the array of `x` with its elements solved. -/
public theorem trsvUpperData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvUpperData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvUpper d A x i := by
  rw [trsvUpperData_eq_iterRange, iterRange_trsvUpperStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp

/-! ## `trsv` -/

/-- The solution of `A * y = x` for the triangle `uplo` of `A`, element by element. -/
@[expose] public def trsvSol (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Nat → Float32 :=
  match uplo with
  | .lower => trsvLower d A x
  | .upper => trsvUpper d A x

/-- The array of `trsv`. -/
@[expose] public def trsvData (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  match uplo with
  | .lower => trsvLowerData d A x
  | .upper => trsvUpperData d A x

public theorem trsvData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvData uplo d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvSol uplo d A x i := by
  cases uplo
  · exact trsvUpperData_eq d A x
  · exact trsvLowerData_eq d A x

/--
`trsv uplo d A x` solves `A * y = x` for the triangle `uplo` of `A`, with a unit diagonal if `d` is
`.unit`, by the column-oriented loops of the reference BLAS. For the lower triangle, it solves for
`y[j]` and subtracts `y[j]` times column `j` of `A` from the elements below it, for
`j = 0, …, n - 1`; for the upper triangle, it does the same from `j = n - 1` down to `0`, for the
elements above. It updates `x` in place when its array is not shared, and leaves the elements of
the array outside `x` unchanged. It reads only the triangle `uplo` of `A`, and not its diagonal
when `d` is `.unit`. Like the reference BLAS, it doesn't check for a zero on the diagonal.
-/
@[expose] public def trsv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Vec n where
  data := trsvData uplo d A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [trsvData_eq, size_modifyAt]; exact x.bound

/-- The array of `trsv uplo d A x` is the array of `x` with its elements solved. -/
public theorem data_trsv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsv uplo d A x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvSol uplo d A x i :=
  trsvData_eq uplo d A x

@[simp] public theorem off_trsv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsv uplo d A x).off = x.off := rfl

@[simp] public theorem inc_trsv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsv uplo d A x).inc = x.inc := rfl

/-- Element `i` of `trsv uplo d A x` is element `i` of the model. -/
public theorem getElem_trsv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (h : i < n) : (trsv uplo d A x)[i] = trsvSol uplo d A x i :=
  Vec.getElem_of_data_eq_modifyAt _ (data_trsv uplo d A x) rfl rfl i h

/--
Element `i` of `y = trsv .lower d A x` is `x[i]`, minus the terms `y[l] * A[i, l]` for
`l = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal is unit: forward substitution, in the
order of the loops.
-/
public theorem getElem_trsv_lower (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat) (h : i < n) :
    (trsv .lower d A x)[i] = d.apply (Nat.fold i (fun l hl s =>
      s - (trsv .lower d A x)[l]'(by lia) * A[(i, l)]'⟨h, by lia⟩) x[i]) A[(i, i)] := by
  rw [getElem_trsv _ _ _ _ _ h, trsvSol, trsvLower_eq d A x h]
  congr
  funext l hl s
  rw [getElem_trsv _ _ _ _ _ (by lia), trsvSol]

/--
Element `i` of `y = trsv .upper d A x` is `x[i]`, minus the terms `y[l] * A[i, l]` for
`l = n - 1, …, i + 1`, divided by `A[i, i]` unless the diagonal is unit: back substitution, in the
order of the loops.
-/
public theorem getElem_trsv_upper (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat) (h : i < n) :
    (trsv .upper d A x)[i] = d.apply (Nat.fold (n - 1 - i) (fun t _ s =>
      s - (trsv .upper d A x)[n - 1 - t]'(by lia) * A[(i, n - 1 - t)]'⟨h, by lia⟩) x[i])
        A[(i, i)] := by
  rw [getElem_trsv _ _ _ _ _ h, trsvSol, trsvUpper_eq d A x h]
  congr
  funext t ht s
  rw [getElem_trsv _ _ _ _ _ (by lia), trsvSol]

end Mat

end BLAS.Float32
