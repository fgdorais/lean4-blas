/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Tpmv
public import BLAS.Float64.Trsv
import all BLAS.Internal

/-!
# Packed triangular solve

`Mat.tpsv uplo d ap x` solves `A * y = x` and `Mat.tpsvT uplo d ap x` solves `Aᵀ * y = x`, over
`x`, for the triangular matrix `A` whose triangle `uplo` is packed in `ap` as for `Mat.tpmv`, by the
loops of the reference BLAS (`dtpsv`), as `Mat.trsv` and `Mat.trsvT` do for a full triangle. As
there, the reference BLAS doesn't test for singularity: a zero on the diagonal gives infinities or
NaNs. The reference BLAS master doesn't skip the columns with a zero element of the solution
either, so neither do these.

The specification of each element of the solution is recursive, in the solution: the element `i` is
`x[i]`, minus the terms of the other elements of its row (its column for `tpsvT`) in the triangle,
times the elements of the solution that they multiply, in the order of the loops, divided by the
diagonal unless it is unit.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {n : Nat}

/-! ## The loops -/

/--
A loop whose step `i` only maps its variable, by `g i` with the array `a`, leaves `a` unchanged.
-/
private theorem iterRange_fst (g : Nat → Float64Array → Float → Float) (k : Nat) (t : Float)
    (a : Float64Array) :
    iterRange (fun i p => (g i p.2 p.1, p.2)) 0 k (t, a) =
      (Nat.fold k (fun i _ s => g i a s) t, a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, Nat.fold_succ]

/-- The `USize` index of the row `j + 1 + l` below the diagonal of column `j`. -/
private theorem below_index (x : Vec n) (hs : x.data.size < USize.size) {k : Nat} {j l : USize}
    (hj : j.toNat < n) (hl : l.toNat < (bandBelow n k j).toNat) :
    (x.off.toUSize + x.inc.toUSize * (j + 1 + l)).toNat = x.off + x.inc * (j.toNat + 1 + l.toNat) :=
  by
  have h := toNat_bandBelow_add (Nat.lt_of_le_of_lt x.le_size hs) hj hl
  rw [x.toNat_index hs (by rw [h.1]; exact h.2), h.1]

/-! ## The models -/

/--
Element `i` of the solution of `A * y = x` for the packed upper triangle `A`, on the arrays: `x[i]`,
minus the terms `y[j] * A[i, j]` for `j = n - 1` down to `i + 1`, divided by `A[i, i]` unless the
diagonal is unit.
-/
public def tpsvUpper (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat) : Float :=
  d.apply (Nat.fold (n - 1 - i) (fun t _ht s =>
      s - tpsvUpper d ap x (n - 1 - t) * ap.data[ap.off + ap.inc * upIdx (n - 1 - t) i]!)
    x.data[x.off + x.inc * i]!) ap.data[ap.off + ap.inc * upIdx i i]!
termination_by n - i
decreasing_by lia

/--
Element `i` of the solution of `A * y = x` for the packed lower triangle `A`, on the arrays: `x[i]`,
minus the terms `y[j] * A[i, j]` for `j = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal is
unit.
-/
public def tpsvLower (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat) : Float :=
  d.apply (Nat.fold i (fun t _ht s =>
      s - tpsvLower d ap x t * ap.data[ap.off + ap.inc * loIdx n t i]!)
    x.data[x.off + x.inc * i]!) ap.data[ap.off + ap.inc * loIdx n i i]!
termination_by i
decreasing_by lia

/--
Element `j` of the solution of `Aᵀ * y = x` for the packed upper triangle `A`, on the arrays:
`x[j]`, minus the terms `A[i, j] * y[i]` for `i = 0, …, j - 1`, divided by `A[j, j]` unless the
diagonal is unit.
-/
public def tpsvTUpper (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) : Float :=
  d.apply (Nat.fold j (fun t _ht s =>
      s - ap.data[ap.off + ap.inc * upIdx j t]! * tpsvTUpper d ap x t)
    x.data[x.off + x.inc * j]!) ap.data[ap.off + ap.inc * upIdx j j]!
termination_by j
decreasing_by lia

/--
Element `j` of the solution of `Aᵀ * y = x` for the packed lower triangle `A`, on the arrays:
`x[j]`, minus the terms `A[i, j] * y[i]` for `i = n - 1` down to `j + 1`, divided by `A[j, j]`
unless the diagonal is unit.
-/
public def tpsvTLower (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) : Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ht s =>
      s - ap.data[ap.off + ap.inc * loIdx n j (n - 1 - t)]! * tpsvTLower d ap x (n - 1 - t))
    x.data[x.off + x.inc * j]!) ap.data[ap.off + ap.inc * loIdx n j j]!
termination_by n - j
decreasing_by lia

/-! ## The upper triangle -/

/--
The map of step `j` of the upper solve on element `i`, when `x[j]` is `t` as the step starts:
divide element `j` by the diagonal, and subtract the quotient times column `j` from the elements
above it.
-/
@[expose] public def tpsvUpperG (d : Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat) (t : Float)
    (i : Nat) (v : Float) : Float :=
  if i = j then d.apply v ap.data[ap.off + ap.inc * upIdx j j]!
  else if i < j then
    v - d.apply t ap.data[ap.off + ap.inc * upIdx j j]! * ap.data[ap.off + ap.inc * upIdx j i]!
  else v

/-- The step `kk` of the upper solve, for the column `n - 1 - kk`. -/
@[expose] public def tpsvUpperStep (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (kk : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n (tpsvUpperG d ap (n - 1 - kk) c[x.stride.idx (n - 1 - kk)]!)

/-- The array of the upper solve. -/
public def tpsvUpperData (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Float64Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let po := ap.off.toUSize
    let pc := ap.inc.toUSize
    (inplace a do
      for kk in 0...nu do
        have hj : (nu - 1 - kk).toNat = n - 1 - kk.toNat := by grind
        have hjn : (nu - 1 - kk).toNat < n := by lia
        have hq : (o + c * (nu - 1 - kk)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        have hd := toNat_packedUp_add hn hjn (l := nu - 1 - kk) (Nat.le_refl _)
        let s := d.apply a[o + c * (nu - 1 - kk)]
          (ap.uget po pc rfl rfl hs.1 (packedUp (nu - 1 - kk) + (nu - 1 - kk)) (hd.1 ▸ hd.2))
        a[o + c * (nu - 1 - kk)] := s
        for l in 0...nu - 1 - kk do
          have hp := toNat_packedUp_add hn hjn (l := l) (Nat.le_of_lt (by assumption))
          have hq' : (o + c * l).toNat < a.size :=
            x.toNat_index_lt hs.2 (Nat.lt_trans (by assumption) hjn)
          a[o + c * l] := a[o + c * l] -
            s * ap.uget po pc rfl rfl hs.1 (packedUp (nu - 1 - kk) + l) (hp.1 ▸ hp.2)).2
  else iterRange (tpsvUpperStep d ap x) 0 n x.data

public theorem tpsvUpperData_eq_iterRange (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvUpperData d ap x = iterRange (tpsvUpperStep d ap x) 0 n x.data := by
  unfold tpsvUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    have hF : ∀ j a, (tpsvUpperStep d ap x j a).size = a.size := fun _ _ => by
      unfold tpsvUpperStep; exact size_modifyAt _ _ _ _ _
    rw [Tail.run_forInFrom_unit (F := tpsvUpperStep d ap x) (hF := hF)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro kk _ hkk next a h
      rw [hnu] at hkk
      have hj : (n.toUSize - 1 - kk).toNat = n - 1 - kk.toNat := by grind
      have hjn : (n.toUSize - 1 - kk).toNat < n := by lia
      have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk)).toNat =
          x.off + x.inc * (n - 1 - kk.toNat) := by
        rw [x.toNat_index hs.2 hjn, hj]
      have hd := toNat_packedUp_add hn hjn (l := n.toUSize - 1 - kk) (Nat.le_refl _)
      simp only [Tail.run_readThen, Tail.run_writeThen]
      rw [Tail.run_forInFrom_modify
        (e := fun l => x.off.toUSize + x.inc.toUSize * l)
        (idx := fun l => x.off + x.inc * (0 + l))
        (he := fun l _ hl => by rw [x.toNat_index hs.2 (by lia), Nat.zero_add])
        (G := fun l v => v - d.apply a[x.off + x.inc * (n - 1 - kk.toNat)]!
          ap.data[ap.off + ap.inc * ((n - 1 - kk.toNat) * (n - 1 - kk.toNat + 1) / 2 +
            (n - 1 - kk.toNat))]! *
          ap.data[ap.off + ap.inc * ((n - 1 - kk.toNat) * (n - 1 - kk.toNat + 1) / 2 + l)]!)]
      · congr 1
        simp only [USize.toNat_zero, hj, Vec.uget_eq_getElem, Vec.getElem_def, hp, hd.1]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [modifyAt_band_set! x a h 0 (n - 1 - kk.toNat) (n - 1 - kk.toNat) (by lia) (by lia)
          (by lia) _ (fun v => d.apply v ap.data[ap.off + ap.inc *
            ((n - 1 - kk.toNat) * (n - 1 - kk.toNat + 1) / 2 + (n - 1 - kk.toNat))]!),
          tpsvUpperStep]
        apply modifyAt_congr_fun
        intro i v _ _
        simp only [tpsvUpperG, Vec.idx_stride, upIdx, Nat.zero_le, true_and, Nat.zero_add,
          Nat.sub_zero]
      · intro l _ hl v
        rw [hj] at hl
        have hq := toNat_packedUp_add hn hjn (l := l) (by lia)
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, hp, hq.1, hd.1, hj, getElem_eq_getElem!]
  · rfl

/-- The array of the upper solve is the array of `x` with its elements solved. -/
public theorem tpsvUpperData_eq (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvUpperData d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpsvUpper d ap x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tpsvUpperData_eq_iterRange]
  refine (iterRange_modifyAt_self x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun kk => n - 1 - kk) n (fun kk hkk => by lia)
    (fun kk => tpsvUpperG d ap (n - 1 - kk))).trans ?_
  rw [modifyAt_eq_read _ _ hinj (fun i _ hi => x.index_lt hi)]
  -- the values that the steps read are the elements of the solution
  have hsol : ∀ m j, n - 1 - j < m → j < n →
      d.apply (selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
        (fun kk => tpsvUpperG d ap (n - 1 - kk)) (n - 1 - j))
          ap.data[ap.off + ap.inc * upIdx j j]! = tpsvUpper d ap x j := by
    intro m
    induction m with
    | zero => intro j h; lia
    | succ m ih =>
      intro j hm hj
      rw [selfRead, show n - 1 - (n - 1 - j) = j by lia]
      rw [show (fun kk (_ : kk < n - 1 - j) v => tpsvUpperG d ap (n - 1 - kk)
            (selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
              (fun kk => tpsvUpperG d ap (n - 1 - kk)) kk) j v) =
          fun kk _ v => if j = n - 1 - kk then
              d.apply v ap.data[ap.off + ap.inc * upIdx (n - 1 - kk) (n - 1 - kk)]!
            else if j < n - 1 - kk then
              (fun c s => s - tpsvUpper d ap x c * ap.data[ap.off + ap.inc * upIdx c j]!)
                (n - 1 - kk) v
            else v from by
        funext kk hkk v
        simp only [tpsvUpperG]
        rw [← ih (n - 1 - kk) (by lia) (by lia), show n - 1 - (n - 1 - kk) = kk by lia]]
      rw [fold_upper_tri_rev_pre hj (fun c s => d.apply s ap.data[ap.off + ap.inc * upIdx c c]!)
        (fun c s => s - tpsvUpper d ap x c * ap.data[ap.off + ap.inc * upIdx c j]!), tpsvUpper]
      rfl
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [show (fun kk (hkk : kk < n) v => tpsvUpperG d ap (n - 1 - kk)
        (selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
          (fun kk => tpsvUpperG d ap (n - 1 - kk)) kk) i v) =
      fun kk _ v => if i = n - 1 - kk then
          d.apply v ap.data[ap.off + ap.inc * upIdx (n - 1 - kk) (n - 1 - kk)]!
        else if i < n - 1 - kk then
          (fun c s => s - tpsvUpper d ap x c * ap.data[ap.off + ap.inc * upIdx c i]!)
            (n - 1 - kk) v
        else v from by
    funext kk hkk v
    simp only [tpsvUpperG]
    rw [← hsol _ (n - 1 - kk) (Nat.lt_succ_self _) (by lia), show n - 1 - (n - 1 - kk) = kk by lia]]
  rw [fold_upper_tri_rev hi (fun c s => d.apply s ap.data[ap.off + ap.inc * upIdx c c]!)
    (fun c s => s - tpsvUpper d ap x c * ap.data[ap.off + ap.inc * upIdx c i]!), tpsvUpper]
  rfl

/-! ## The lower triangle -/

/--
The map of step `j` of the lower solve on element `i`, when `x[j]` is `t` as the step starts:
divide element `j` by the diagonal, and subtract the quotient times column `j` from the elements
below it.
-/
@[expose] public def tpsvLowerG (d : Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat) (t : Float)
    (i : Nat) (v : Float) : Float :=
  if i = j then d.apply v ap.data[ap.off + ap.inc * loIdx n j j]!
  else if j < i then
    v - d.apply t ap.data[ap.off + ap.inc * loIdx n j j]! * ap.data[ap.off + ap.inc * loIdx n j i]!
  else v

/-- The step `j` of the lower solve. -/
@[expose] public def tpsvLowerStep (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (j : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n (tpsvLowerG d ap j c[x.stride.idx j]!)

/-- The array of the lower solve. -/
public def tpsvLowerData (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Float64Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let po := ap.off.toUSize
    let pc := ap.inc.toUSize
    (inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        have hq : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 hjn
        have hd := toNat_packedLo hn hjn
        let s := d.apply a[o + c * j] (ap.uget po pc rfl rfl hs.1 (packedLo n j) (hd.1 ▸ hd.2))
        a[o + c * j] := s
        for l in 0...bandBelow n n j do
          have hp := toNat_packedLo_below hn hn' hjn (by assumption)
          have hi := toNat_bandBelow_add hn' hjn (by assumption)
          have hq' : (o + c * (j + 1 + l)).toNat < a.size := x.toNat_index_lt hs.2 (hi.1 ▸ hi.2)
          a[o + c * (j + 1 + l)] := a[o + c * (j + 1 + l)] -
            s * ap.uget po pc rfl rfl hs.1 (packedLo n j + (1 + l)) (hp.1 ▸ hp.2)).2
  else iterRange (tpsvLowerStep d ap x) 0 n x.data

public theorem tpsvLowerData_eq_iterRange (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvLowerData d ap x = iterRange (tpsvLowerStep d ap x) 0 n x.data := by
  unfold tpsvLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    have hF : ∀ j a, (tpsvLowerStep d ap x j a).size = a.size := fun _ _ => by
      unfold tpsvLowerStep; exact size_modifyAt _ _ _ _ _
    rw [Tail.run_forInFrom_unit (F := tpsvLowerStep d ap x) (hF := hF)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hp := x.toNat_index hs.2 hj
      have hd := toNat_packedLo hn hj
      have hbe : (bandBelow n n j).toNat = n - 1 - j.toNat := by
        rw [toNat_bandBelow hn']; lia
      simp only [Tail.run_readThen, Tail.run_writeThen]
      rw [Tail.run_forInFrom_modify
        (e := fun l => x.off.toUSize + x.inc.toUSize * (j + 1 + l))
        (idx := fun l => x.off + x.inc * (j.toNat + 1 + l))
        (he := fun l _ hl => below_index (k := n) x hs.2 hj hl)
        (G := fun l v => v - d.apply a[x.off + x.inc * j.toNat]!
          ap.data[ap.off + ap.inc * (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2)]! *
          ap.data[ap.off + ap.inc *
            (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + (1 + l))]!)]
      · congr 1
        simp only [USize.toNat_zero, hbe, Vec.uget_eq_getElem, Vec.getElem_def, hp, hd.1]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [modifyAt_band_set! x a h (j.toNat + 1) (n - 1 - j.toNat) j.toNat (by lia) hj
          (by lia) _ (fun v => d.apply v ap.data[ap.off + ap.inc *
            (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2)]!), tpsvLowerStep]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [tpsvLowerG, Vec.idx_stride, loIdx, Nat.sub_self, Nat.add_zero]
        by_cases h₁ : i = j.toNat
        · simp only [h₁, ↓reduceIte]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁),
            ite_eq_right_of_eq_false _ _ (eq_false h₁)]
          by_cases h₂ : j.toNat < i
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
              ite_eq_left_of_eq_true _ _ (eq_true h₂),
              show 1 + (i - (j.toNat + 1)) = i - j.toNat by lia]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia)),
              ite_eq_right_of_eq_false _ _ (eq_false h₂)]
      · intro l _ hl v
        have hl' := toNat_one_add_bandBelow (k := n) hn' hl
        have hq := toNat_packedLo_below hn hn' hj hl
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, hp, hq.1, hd.1, hl'.1,
          getElem_eq_getElem!]
  · rfl

/-- The array of the lower solve is the array of `x` with its elements solved. -/
public theorem tpsvLowerData_eq (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvLowerData d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpsvLower d ap x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tpsvLowerData_eq_iterRange]
  refine (iterRange_modifyAt_self x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun j => j) n (fun j hj => hj) (tpsvLowerG d ap)).trans ?_
  rw [modifyAt_eq_read _ _ hinj (fun i _ hi => x.index_lt hi)]
  -- the values that the steps read are the elements of the solution
  have hsol : ∀ m j, j < m → j < n →
      d.apply (selfRead x.data x.stride.idx (fun j => j) (tpsvLowerG d ap) j)
        ap.data[ap.off + ap.inc * loIdx n j j]! = tpsvLower d ap x j := by
    intro m
    induction m with
    | zero => intro j h; lia
    | succ m ih =>
      intro j hm hj
      rw [selfRead]
      rw [show (fun j' (_ : j' < j) v => tpsvLowerG d ap j'
            (selfRead x.data x.stride.idx (fun j => j) (tpsvLowerG d ap) j') j v) =
          fun j' _ v => if j = j' then d.apply v ap.data[ap.off + ap.inc * loIdx n j' j']!
            else if j' < j then
              (fun c s => s - tpsvLower d ap x c * ap.data[ap.off + ap.inc * loIdx n c j]!) j' v
            else v from by
        funext j' hj' v
        simp only [tpsvLowerG]
        rw [← ih j' (by lia) (by lia)]]
      rw [fold_lower_tri_pre (fun c s => d.apply s ap.data[ap.off + ap.inc * loIdx n c c]!)
        (fun c s => s - tpsvLower d ap x c * ap.data[ap.off + ap.inc * loIdx n c j]!), tpsvLower]
      rfl
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [show (fun j (hj : j < n) v => tpsvLowerG d ap j
        (selfRead x.data x.stride.idx (fun j => j) (tpsvLowerG d ap) j) i v) =
      fun j _ v => if i = j then d.apply v ap.data[ap.off + ap.inc * loIdx n j j]!
        else if j < i then
          (fun c s => s - tpsvLower d ap x c * ap.data[ap.off + ap.inc * loIdx n c i]!) j v
        else v from by
    funext j hj v
    simp only [tpsvLowerG]
    rw [← hsol _ j (Nat.lt_succ_self _) hj]]
  rw [fold_lower_tri hi (fun c s => d.apply s ap.data[ap.off + ap.inc * loIdx n c c]!)
    (fun c s => s - tpsvLower d ap x c * ap.data[ap.off + ap.inc * loIdx n c i]!), tpsvLower]
  rfl

/-! ## The transposed upper triangle -/

/--
The value that the step for column `j` of the transposed upper solve writes at element `j`, from
the elements `get q` of `x`: `get j`, minus the terms `A[i, j] * get i` for `i = 0, …, j - 1`,
divided by `A[j, j]` unless the diagonal is unit.
-/
@[expose] public def tpsvTUpperH (d : Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat)
    (get : Nat → Float) : Float :=
  d.apply (Nat.fold j (fun t _ s => s - ap.data[ap.off + ap.inc * upIdx j t]! * get t) (get j))
    ap.data[ap.off + ap.inc * upIdx j j]!

/-- The step `j` of the transposed upper solve. -/
@[expose] public def tpsvTUpperStep (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (j : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n fun i v =>
    if i = j then tpsvTUpperH d ap j (fun q => c[x.stride.idx q]!) else v

/-- The array of the transposed upper solve. -/
public def tpsvTUpperData (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Float64Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let po := ap.off.toUSize
    let pc := ap.inc.toUSize
    (inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        have hq : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * j]
        for t in 0...j with (s := v) do
          have hp := toNat_packedUp_add hn hjn (l := t) (Nat.le_of_lt (by assumption))
          have hq' : (o + c * t).toNat < a.size :=
            x.toNat_index_lt hs.2 (Nat.lt_trans (by assumption) hjn)
          s := s - ap.uget po pc rfl rfl hs.1 (packedUp j + t) (hp.1 ▸ hp.2) * a[o + c * t]
        have hd := toNat_packedUp_add hn hjn (l := j) (Nat.le_refl _)
        a[o + c * j] := d.apply s (ap.uget po pc rfl rfl hs.1 (packedUp j + j) (hd.1 ▸ hd.2))).2
  else iterRange (tpsvTUpperStep d ap x) 0 n x.data

public theorem tpsvTUpperData_eq_iterRange (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvTUpperData d ap x = iterRange (tpsvTUpperStep d ap x) 0 n x.data := by
  unfold tpsvTUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    have hF : ∀ j a, (tpsvTUpperStep d ap x j a).size = a.size := fun _ _ => by
      unfold tpsvTUpperStep; exact size_modifyAt _ _ _ _ _
    rw [Tail.run_forInFrom_unit (F := tpsvTUpperStep d ap x) (hF := hF)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hp := x.toNat_index hs.2 hj
      have hd := toNat_packedUp_add hn hj (l := j) (Nat.le_refl _)
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 - ap.data[ap.off + ap.inc * upIdx j.toNat t]! * p.2[x.off + x.inc * t]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, iterRange_fst (fun t a s =>
          s - ap.data[ap.off + ap.inc * upIdx j.toNat t]! * a[x.off + x.inc * t]!)]
        congr 1
        simp only [hp, Vec.uget_eq_getElem, Vec.getElem_def, hd.1]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_eq_modifyAt_ite x a h hj, tpsvTUpperStep]
        rfl
      · intro t _ ht next' b a' h'
        have hq := toNat_packedUp_add hn hj (l := t) (by lia)
        have hp' : (x.off.toUSize + x.inc.toUSize * t).toNat = x.off + x.inc * t.toNat :=
          x.toNat_index hs.2 (by lia)
        simp only [Tail.run_readThen, Vec.uget_eq_getElem, Vec.getElem_def, hp', hq.1,
          getElem_eq_getElem!, upIdx]
  · rfl

/-- The array of the transposed upper solve is the array of `x` with its elements solved. -/
public theorem tpsvTUpperData_eq (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvTUpperData d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpsvTUpper d ap x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tpsvTUpperData_eq_iterRange]
  refine (iterRange_write x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun j => j) (fun q => q) (fun j _ => rfl) (fun q _ => rfl)
    (fun j => tpsvTUpperH d ap j) (fun j hj get get' hget => by
      simp only [tpsvTUpperH]
      rw [hget _ hj]
      congr 2
      funext t ht s
      rw [hget _ (by lia)]) (Nat.le_refl n)).trans ?_
  have hsol : ∀ m j, j < m → j < n →
      writeRead x.data x.stride.idx (fun q => q) (fun j => tpsvTUpperH d ap j) j =
        tpsvTUpper d ap x j := by
    intro m
    induction m with
    | zero => intro j h; lia
    | succ m ih =>
      intro j hm hj
      rw [writeRead, tpsvTUpper, tpsvTUpperH, dite_eq_right (Nat.lt_irrefl j)]
      congr 2
      funext t ht s
      rw [dite_eq_left ht, ih _ (by lia) (by lia)]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi), hsol _ i (Nat.lt_succ_self _) hi]

/-! ## The transposed lower triangle -/

/--
The value that the step for column `j` of the transposed lower solve writes at element `j`, from
the elements `get q` of `x`: `get j`, minus the terms `A[i, j] * get i` for `i = n - 1` down to
`j + 1`, divided by `A[j, j]` unless the diagonal is unit.
-/
@[expose] public def tpsvTLowerH (d : Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat)
    (get : Nat → Float) : Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - ap.data[ap.off + ap.inc * loIdx n j (n - 1 - t)]! * get (n - 1 - t)) (get j))
    ap.data[ap.off + ap.inc * loIdx n j j]!

/-- The step `kk` of the transposed lower solve, for the column `n - 1 - kk`. -/
@[expose] public def tpsvTLowerStep (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (kk : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n fun i v =>
    if i = n - 1 - kk then tpsvTLowerH d ap (n - 1 - kk) (fun q => c[x.stride.idx q]!) else v

/-- The array of the transposed lower solve. -/
public def tpsvTLowerData (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Float64Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let po := ap.off.toUSize
    let pc := ap.inc.toUSize
    (inplace a do
      for kk in 0...nu do
        have hkk : kk.toNat < n := by lia
        have hjn : (nu - 1 - kk).toNat < n := by grind
        have hq : (o + c * (nu - 1 - kk)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - kk)]
        let cnt := bandBelow n n (nu - 1 - kk)
        for t in 0...cnt with (s := v) do
          have hi := toNat_rev_bandBelow_sub hn' hkk (by assumption)
          have hp := toNat_packedLo_rev_sub hn hn' hkk (by assumption)
          have hq' : (o + c * (nu - 1 - kk + cnt - t)).toNat < a.size :=
            x.toNat_index_lt hs.2 (hi.1 ▸ hi.2)
          s := s - ap.uget po pc rfl rfl hs.1 (packedLo n (nu - 1 - kk) + (cnt - t)) (hp.1 ▸ hp.2) *
            a[o + c * (nu - 1 - kk + cnt - t)]
        have hd := toNat_packedLo hn hjn
        a[o + c * (nu - 1 - kk)] :=
          d.apply s (ap.uget po pc rfl rfl hs.1 (packedLo n (nu - 1 - kk)) (hd.1 ▸ hd.2))).2
  else iterRange (tpsvTLowerStep d ap x) 0 n x.data

public theorem tpsvTLowerData_eq_iterRange (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvTLowerData d ap x = iterRange (tpsvTLowerStep d ap x) 0 n x.data := by
  unfold tpsvTLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    have hF : ∀ j a, (tpsvTLowerStep d ap x j a).size = a.size := fun _ _ => by
      unfold tpsvTLowerStep; exact size_modifyAt _ _ _ _ _
    rw [Tail.run_forInFrom_unit (F := tpsvTLowerStep d ap x) (hF := hF)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro kk _ hkk next a h
      rw [hnu] at hkk
      have hj : (n.toUSize - 1 - kk).toNat = n - 1 - kk.toNat := by grind
      have hjn : (n.toUSize - 1 - kk).toNat < n := by lia
      have hbe : (bandBelow n n (n.toUSize - 1 - kk)).toNat = n - 1 - (n - 1 - kk.toNat) := by
        rw [toNat_bandBelow hn', hj]; lia
      have hd := toNat_packedLo hn hjn
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 - ap.data[ap.off + ap.inc * loIdx n (n - 1 - kk.toNat) (n - 1 - t)]! *
            p.2[x.off + x.inc * (n - 1 - t)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, hbe, iterRange_fst (fun t a s =>
          s - ap.data[ap.off + ap.inc * loIdx n (n - 1 - kk.toNat) (n - 1 - t)]! *
            a[x.off + x.inc * (n - 1 - t)]!)]
        congr 1
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk)).toNat =
            x.off + x.inc * (n - 1 - kk.toNat) := by
          rw [x.toNat_index hs.2 hjn, hj]
        simp only [hp, Vec.uget_eq_getElem, Vec.getElem_def, hd.1, hj]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_eq_modifyAt_ite x a h (by lia), tpsvTLowerStep]
        simp only [tpsvTLowerH, loIdx, Nat.sub_self, Nat.add_zero, Vec.idx_stride]
      · intro t _ ht next' b a' h'
        have hi := toNat_rev_bandBelow_sub hn' hkk ht
        have hq := toNat_packedLo_rev_sub hn hn' hkk ht
        have hp : (x.off.toUSize + x.inc.toUSize *
              (n.toUSize - 1 - kk + bandBelow n n (n.toUSize - 1 - kk) - t)).toNat =
            x.off + x.inc * (n - 1 - t.toNat) := by
          rw [x.toNat_index hs.2 (hi.1 ▸ hi.2), hi.1]
        simp only [Tail.run_readThen, Vec.uget_eq_getElem, Vec.getElem_def, hp, hq.1,
          getElem_eq_getElem!, loIdx]
  · rfl

/-- The array of the transposed lower solve is the array of `x` with its elements solved. -/
public theorem tpsvTLowerData_eq (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvTLowerData d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpsvTLower d ap x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tpsvTLowerData_eq_iterRange]
  refine (iterRange_write x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun kk => n - 1 - kk) (fun q => n - 1 - q) (fun kk hkk => by lia) (fun q hq => by lia)
    (fun kk => tpsvTLowerH d ap (n - 1 - kk)) (fun kk hkk get get' hget => by
      simp only [tpsvTLowerH]
      rw [hget _ (by lia)]
      congr 2
      funext t ht s
      rw [hget _ (by lia)]) (Nat.le_refl n)).trans ?_
  have hsol : ∀ m j, n - 1 - j < m → j < n →
      writeRead x.data x.stride.idx (fun q => n - 1 - q) (fun kk => tpsvTLowerH d ap (n - 1 - kk))
        (n - 1 - j) = tpsvTLower d ap x j := by
    intro m
    induction m with
    | zero => intro j h; lia
    | succ m ih =>
      intro j hm hj
      rw [writeRead, show n - 1 - (n - 1 - j) = j by lia, tpsvTLower, tpsvTLowerH,
        dite_eq_right (Nat.lt_irrefl (n - 1 - j))]
      congr 2
      funext t ht s
      rw [dite_eq_left (show n - 1 - (n - 1 - t) < n - 1 - j by lia),
        ih _ (by lia) (by lia)]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)), hsol _ i (Nat.lt_succ_self _) hi]

/-! ## `tpsv` and `tpsvT` -/

/-- The solution of `A * y = x` for the packed triangle `uplo` `A`, element by element. -/
@[expose] public def tpsvSol (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => tpsvUpper d ap x
  | .lower => tpsvLower d ap x

/-- The array of `tpsv`. -/
@[expose] public def tpsvData (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Float64Array :=
  match uplo with
  | .upper => tpsvUpperData d ap x
  | .lower => tpsvLowerData d ap x

public theorem tpsvData_eq (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvData uplo d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpsvSol uplo d ap x i := by
  cases uplo
  · exact tpsvUpperData_eq d ap x
  · exact tpsvLowerData_eq d ap x

/--
`tpsv uplo d ap x` is the solution `y` of `A * y = x` for the triangular matrix `A` whose triangle
`uplo` is packed in `ap`, with a unit diagonal if `d` is `.unit`, by the column-oriented loops of
the reference BLAS (`dtpsv` with `TRANS = 'N'`). For the upper triangle, it divides element `j` by
the diagonal and subtracts the quotient times column `j` from the elements above `j`, for
`j = n - 1` down to `0`; for the lower triangle, it does the same for `j = 0, …, n - 1`, with the
elements below. It updates `x` in place when its array is not shared, leaves the elements of the
array outside `x` unchanged, and does not read the diagonal when `d` is `.unit`.
-/
@[expose] public def tpsv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Vec n where
  data := tpsvData uplo d ap x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [tpsvData_eq, size_modifyAt]; exact x.bound

/-- The array of `tpsv uplo d ap x` is the array of `x` with its elements solved. -/
public theorem data_tpsv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    (tpsv uplo d ap x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => tpsvSol uplo d ap x i :=
  tpsvData_eq uplo d ap x

@[simp] public theorem off_tpsv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    (tpsv uplo d ap x).off = x.off := rfl

@[simp] public theorem inc_tpsv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    (tpsv uplo d ap x).inc = x.inc := rfl

/-- Element `i` of `tpsv uplo d ap x` is element `i` of the model. -/
public theorem getElem_tpsv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) (h : i < n) : (tpsv uplo d ap x)[i] = tpsvSol uplo d ap x i :=
  Vec.getElem_of_data_eq_modifyAt _ (data_tpsv uplo d ap x) rfl rfl i h

/--
Element `i` of `y = tpsv .upper d ap x` is `x[i]`, minus the terms `y[j] * A[i, j]` for `j = n - 1`
down to `i + 1`, divided by `A[i, i]` unless the diagonal is unit, where `A[i, j]` is
`ap[upIdx j i]`: back substitution, in the order of the loops.
-/
public theorem getElem_tpsv_upper (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat)
    (h : i < n) :
    (tpsv .upper d ap x)[i] = d.apply (Nat.fold (n - 1 - i) (fun t _ s =>
      s - (tpsv .upper d ap x)[n - 1 - t]'(by lia) *
        ap[upIdx (n - 1 - t) i]'(upIdx_lt (by lia) (by lia))) x[i])
      (ap[upIdx i i]'(upIdx_lt (Nat.le_refl i) h)) := by
  rw [getElem_tpsv _ _ _ _ _ h, tpsvSol, tpsvUpper, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (Nat.le_refl i) h))]
  congr 2
  funext t ht s
  rw [getElem_tpsv _ _ _ _ _ (by lia), tpsvSol,
    getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (by lia) (by lia)))]
  rfl

/--
Element `i` of `y = tpsv .lower d ap x` is `x[i]`, minus the terms `y[j] * A[i, j]` for
`j = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal is unit, where `A[i, j]` is
`ap[loIdx n j i]`: forward substitution, in the order of the loops.
-/
public theorem getElem_tpsv_lower (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat)
    (h : i < n) :
    (tpsv .lower d ap x)[i] = d.apply (Nat.fold i (fun t _ s =>
      s - (tpsv .lower d ap x)[t]'(by lia) * ap[loIdx n t i]'(loIdx_lt (by lia) h)) x[i])
      (ap[loIdx n i i]'(loIdx_lt (Nat.le_refl i) h)) := by
  rw [getElem_tpsv _ _ _ _ _ h, tpsvSol, tpsvLower, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (Nat.le_refl i) h))]
  congr 2
  funext t ht s
  rw [getElem_tpsv _ _ _ _ _ (by lia), tpsvSol,
    getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (by lia) h))]
  rfl

/-- The solution of `Aᵀ * y = x` for the packed triangle `uplo` `A`, element by element. -/
@[expose] public def tpsvTSol (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => tpsvTUpper d ap x
  | .lower => tpsvTLower d ap x

/-- The array of `tpsvT`. -/
@[expose] public def tpsvTData (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Float64Array :=
  match uplo with
  | .upper => tpsvTUpperData d ap x
  | .lower => tpsvTLowerData d ap x

public theorem tpsvTData_eq (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpsvTData uplo d ap x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tpsvTSol uplo d ap x i := by
  cases uplo
  · exact tpsvTUpperData_eq d ap x
  · exact tpsvTLowerData_eq d ap x

/--
`tpsvT uplo d ap x` is the solution `y` of `Aᵀ * y = x` for the triangular matrix `A` whose
triangle `uplo` is packed in `ap`, with a unit diagonal if `d` is `.unit`, by the loops of the
reference BLAS (`dtpsv` with `TRANS = 'T'`). For the upper triangle, it sets element `j` to `x[j]`
minus the dot product of column `j` above the diagonal, from the top down, and of the solution,
divided by the diagonal, for `j = 0, …, n - 1`; for the lower triangle, it does the same for
`j = n - 1` down to `0`, with the column below the diagonal, from the bottom up. It updates `x` in
place when its array is not shared, leaves the elements of the array outside `x` unchanged, and
does not read the diagonal when `d` is `.unit`.
-/
@[expose] public def tpsvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Vec n where
  data := tpsvTData uplo d ap x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [tpsvTData_eq, size_modifyAt]; exact x.bound

/-- The array of `tpsvT uplo d ap x` is the array of `x` with its elements solved. -/
public theorem data_tpsvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    (tpsvT uplo d ap x).data =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tpsvTSol uplo d ap x i :=
  tpsvTData_eq uplo d ap x

@[simp] public theorem off_tpsvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : (tpsvT uplo d ap x).off = x.off := rfl

@[simp] public theorem inc_tpsvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : (tpsvT uplo d ap x).inc = x.inc := rfl

/-- Element `j` of `tpsvT uplo d ap x` is element `j` of the model. -/
public theorem getElem_tpsvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (j : Nat) (h : j < n) : (tpsvT uplo d ap x)[j] = tpsvTSol uplo d ap x j :=
  Vec.getElem_of_data_eq_modifyAt _ (data_tpsvT uplo d ap x) rfl rfl j h

/--
Element `j` of `y = tpsvT .upper d ap x` is `x[j]`, minus the terms `A[i, j] * y[i]` for
`i = 0, …, j - 1`, divided by `A[j, j]` unless the diagonal is unit, where `A[i, j]` is
`ap[upIdx j i]`: forward substitution, in the order of the loops.
-/
public theorem getElem_tpsvT_upper (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat)
    (h : j < n) :
    (tpsvT .upper d ap x)[j] = d.apply (Nat.fold j (fun t _ s =>
      s - ap[upIdx j t]'(upIdx_lt (by lia) h) * (tpsvT .upper d ap x)[t]'(by lia)) x[j])
      (ap[upIdx j j]'(upIdx_lt (Nat.le_refl j) h)) := by
  rw [getElem_tpsvT _ _ _ _ _ h, tpsvTSol, tpsvTUpper, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (Nat.le_refl j) h))]
  congr 2
  funext t ht s
  rw [getElem_tpsvT _ _ _ _ _ (by lia), tpsvTSol,
    getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (by lia) h))]
  rfl

/--
Element `j` of `y = tpsvT .lower d ap x` is `x[j]`, minus the terms `A[i, j] * y[i]` for
`i = n - 1` down to `j + 1`, divided by `A[j, j]` unless the diagonal is unit, where `A[i, j]` is
`ap[loIdx n j i]`: back substitution, in the order of the loops.
-/
public theorem getElem_tpsvT_lower (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat)
    (h : j < n) :
    (tpsvT .lower d ap x)[j] = d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - ap[loIdx n j (n - 1 - t)]'(loIdx_lt (by lia) (by lia)) *
        (tpsvT .lower d ap x)[n - 1 - t]'(by lia)) x[j])
      (ap[loIdx n j j]'(loIdx_lt (Nat.le_refl j) h)) := by
  rw [getElem_tpsvT _ _ _ _ _ h, tpsvTSol, tpsvTLower, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (Nat.le_refl j) h))]
  congr 2
  funext t ht s
  rw [getElem_tpsvT _ _ _ _ _ (by lia), tpsvTSol,
    getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (by lia) (by lia)))]
  rfl

end Mat

end BLAS.Float64
