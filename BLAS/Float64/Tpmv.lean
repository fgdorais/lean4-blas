/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Packed
public import BLAS.Float64.Trmv
import all BLAS.Internal

/-!
# Packed triangular matrix-vector product

`Mat.tpmv uplo d ap x` computes `A * x` and `Mat.tpmvT uplo d ap x` computes `Aᵀ * x`, over `x`,
for the triangular matrix `A` whose triangle `uplo` is packed in `ap : Vec (n * (n + 1) / 2)` (see
`BLAS.Float64.Packed`), by the loops of the reference BLAS (`dtpmv`), as `Mat.trmv` and
`Mat.trmvT` do for a triangle in a full matrix. Each element of the result is its diagonal term,
`x[i] * A[i, i]` or `x[i]` for a unit diagonal, plus the terms of the other elements of its row (its
column for `tpmvT`) in the triangle, in the order of the loops.
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

/-! ## The upper triangle -/

/--
The map of step `j` of the upper product on element `i`, when `x[j]` is `t` as the step starts:
multiply element `j` by the diagonal, and add `t` times column `j` to the elements above it.
-/
@[expose] public def tpmvUpperG (d : Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat) (t : Float)
    (i : Nat) (v : Float) : Float :=
  if i = j then d.mul v ap.data[ap.off + ap.inc * upIdx j j]!
  else if i < j then v + t * ap.data[ap.off + ap.inc * upIdx j i]!
  else v

/-- The step `j` of the upper product. -/
@[expose] public def tpmvUpperStep (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n (tpmvUpperG d ap j c[x.stride.idx j]!)

/-- The array of the upper product. -/
public def tpmvUpperData (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Float64Array :=
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
        let t := a[o + c * j]
        for l in 0...j do
          have hp := toNat_packedUp_add hn hjn (l := l) (by lia)
          have hq' : (o + c * l).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
          a[o + c * l] := a[o + c * l] +
            t * ap.uget po pc rfl rfl hs.1 (packedUp j + l) (hp.1 ▸ hp.2)
        have hp := toNat_packedUp_add hn hjn (l := j) (Nat.le_refl _)
        a[o + c * j] :=
          d.mul a[o + c * j] (ap.uget po pc rfl rfl hs.1 (packedUp j + j) (hp.1 ▸ hp.2))).2
  else iterRange (tpmvUpperStep d ap x) 0 n x.data

public theorem tpmvUpperData_eq_iterRange (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvUpperData d ap x = iterRange (tpmvUpperStep d ap x) 0 n x.data := by
  unfold tpmvUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    have hF : ∀ j a, (tpmvUpperStep d ap x j a).size = a.size := fun _ _ => by
      unfold tpmvUpperStep; exact size_modifyAt _ _ _ _ _
    rw [Tail.run_forInFrom_unit (F := tpmvUpperStep d ap x) (hF := hF)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hp := x.toNat_index hs.2 hj
      have hd := toNat_packedUp_add hn hj (l := j) (Nat.le_refl _)
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom_modify
        (e := fun l => x.off.toUSize + x.inc.toUSize * l)
        (idx := fun l => x.off + x.inc * (0 + l))
        (he := fun l _ hl => by rw [x.toNat_index hs.2 (by lia), Nat.zero_add])
        (G := fun l v => v + a[x.off + x.inc * j.toNat]! *
          ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + l)]!)]
      · simp only [Tail.run_readThen, Tail.run_writeThen]
        congr 1
        simp only [USize.toNat_zero, Vec.uget_eq_getElem, Vec.getElem_def, hp, hd.1]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_modifyAt_band x a h 0 j.toNat j.toNat (by lia) hj (by lia) _
          (fun v => d.mul v ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + j.toNat)]!),
          tpmvUpperStep]
        apply modifyAt_congr_fun
        intro i v _ _
        simp only [tpmvUpperG, Vec.idx_stride, upIdx, Nat.zero_le, true_and, Nat.zero_add,
          Nat.sub_zero]
      · intro l _ hl v
        have hq := toNat_packedUp_add hn hj (l := l) (by lia)
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, hp, hq.1, getElem_eq_getElem!]
  · rfl

/--
Element `i` of `A * x` for the packed upper triangle `A`, on the arrays: `x[i] * A[i, i]`, or `x[i]`
for a unit diagonal, plus the terms `x[j] * A[i, j]` for `j = i + 1, …, n - 1`.
-/
@[expose] public def tpmvUpper (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat) :
    Float :=
  Nat.fold (n - 1 - i) (fun t _ s =>
      s + x.data[x.off + x.inc * (i + 1 + t)]! * ap.data[ap.off + ap.inc * upIdx (i + 1 + t) i]!)
    (d.mul x.data[x.off + x.inc * i]! ap.data[ap.off + ap.inc * upIdx i i]!)

/-- The array of the upper product is the array of `x` with its elements multiplied. -/
public theorem tpmvUpperData_eq (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvUpperData d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpmvUpper d ap x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tpmvUpperData_eq_iterRange]
  refine (iterRange_modifyAt_self x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun j => j) n (fun j hj => hj) (tpmvUpperG d ap)).trans ?_
  rw [modifyAt_eq_read _ _ hinj (fun i _ hi => x.index_lt hi)]
  apply modifyAt_congr_fun
  intro i v _ hi
  have hread : ∀ j, j < n → selfRead x.data x.stride.idx (fun j => j) (tpmvUpperG d ap) j =
      x.data[x.off + x.inc * j]! := fun j _ =>
    selfRead_eq_of_fix _ _ _ _ fun j' hj' t v => by
      simp only [tpmvUpperG]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia)),
        ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
  rw [show (fun j (hj : j < n) v => tpmvUpperG d ap j
        (selfRead x.data x.stride.idx (fun j => j) (tpmvUpperG d ap) j) i v) =
      fun j _ v => tpmvUpperG d ap j x.data[x.off + x.inc * j]! i v from by
    funext j hj v; rw [hread j hj]]
  simp only [tpmvUpperG]
  rw [fold_upper_tri hi (fun j s => d.mul s ap.data[ap.off + ap.inc * upIdx j j]!)
    (fun j s => s + x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * upIdx j i]!),
    tpmvUpper]
  rfl

/-! ## The lower triangle -/

/-- The `USize` index of the row `j + 1 + l` below the diagonal of column `j`. -/
private theorem below_index (x : Vec n) (hs : x.data.size < USize.size) {k : Nat} {j l : USize}
    (hj : j.toNat < n) (hl : l.toNat < (bandBelow n k j).toNat) :
    (x.off.toUSize + x.inc.toUSize * (j + 1 + l)).toNat = x.off + x.inc * (j.toNat + 1 + l.toNat) :=
  by
  have h := toNat_bandBelow_add (Nat.lt_of_le_of_lt x.le_size hs) hj hl
  rw [x.toNat_index hs (by rw [h.1]; exact h.2), h.1]

/--
The map of step `j` of the lower product on element `i`, when `x[j]` is `t` as the step starts:
multiply element `j` by the diagonal, and add `t` times column `j` to the elements below it.
-/
@[expose] public def tpmvLowerG (d : Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat) (t : Float)
    (i : Nat) (v : Float) : Float :=
  if i = j then d.mul v ap.data[ap.off + ap.inc * loIdx n j j]!
  else if j < i then v + t * ap.data[ap.off + ap.inc * loIdx n j i]!
  else v

/-- The step `kk` of the lower product, for the column `n - 1 - kk`. -/
@[expose] public def tpmvLowerStep (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (kk : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n (tpmvLowerG d ap (n - 1 - kk) c[x.stride.idx (n - 1 - kk)]!)

/-- The array of the lower product. -/
public def tpmvLowerData (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Float64Array :=
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
        have hj : (nu - 1 - kk).toNat = n - 1 - kk.toNat := by grind
        have hjn : (nu - 1 - kk).toNat < n := by lia
        have hq : (o + c * (nu - 1 - kk)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let t := a[o + c * (nu - 1 - kk)]
        for l in 0...bandBelow n n (nu - 1 - kk) do
          have hp := toNat_packedLo_below hn hn' hjn (by assumption)
          have hi := toNat_bandBelow_add hn' hjn (by assumption)
          have hq' : (o + c * (nu - 1 - kk + 1 + l)).toNat < a.size :=
            x.toNat_index_lt hs.2 (hi.1 ▸ hi.2)
          a[o + c * (nu - 1 - kk + 1 + l)] := a[o + c * (nu - 1 - kk + 1 + l)] +
            t * ap.uget po pc rfl rfl hs.1 (packedLo n (nu - 1 - kk) + (1 + l)) (hp.1 ▸ hp.2)
        have hp := toNat_packedLo hn hjn
        a[o + c * (nu - 1 - kk)] := d.mul a[o + c * (nu - 1 - kk)]
          (ap.uget po pc rfl rfl hs.1 (packedLo n (nu - 1 - kk)) (hp.1 ▸ hp.2))).2
  else iterRange (tpmvLowerStep d ap x) 0 n x.data

public theorem tpmvLowerData_eq_iterRange (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvLowerData d ap x = iterRange (tpmvLowerStep d ap x) 0 n x.data := by
  unfold tpmvLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    have hF : ∀ j a, (tpmvLowerStep d ap x j a).size = a.size := fun _ _ => by
      unfold tpmvLowerStep; exact size_modifyAt _ _ _ _ _
    rw [Tail.run_forInFrom_unit (F := tpmvLowerStep d ap x) (hF := hF)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro kk _ hkk next a h
      rw [hnu] at hkk
      have hj : (n.toUSize - 1 - kk).toNat = n - 1 - kk.toNat := by grind
      have hjn : (n.toUSize - 1 - kk).toNat < n := by lia
      have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk)).toNat =
          x.off + x.inc * (n - 1 - kk.toNat) := by
        rw [x.toNat_index hs.2 hjn, hj]
      have hd := toNat_packedLo hn hjn
      have hbe : (bandBelow n n (n.toUSize - 1 - kk)).toNat = kk.toNat := by
        rw [toNat_bandBelow hn', hj]; lia
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom_modify
        (e := fun l => x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk + 1 + l))
        (idx := fun l => x.off + x.inc * (n - 1 - kk.toNat + 1 + l))
        (he := fun l _ hl => by rw [below_index (k := n) x hs.2 hjn hl, hj])
        (G := fun l v => v + a[x.off + x.inc * (n - 1 - kk.toNat)]! *
          ap.data[ap.off + ap.inc * (n * (n + 1) / 2 - (n - (n - 1 - kk.toNat)) *
            (n - (n - 1 - kk.toNat) + 1) / 2 + (1 + l))]!)]
      · simp only [Tail.run_readThen, Tail.run_writeThen]
        congr 1
        simp only [USize.toNat_zero, Vec.uget_eq_getElem, Vec.getElem_def, hp, hd.1, hj, hbe]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_modifyAt_band x a h (n - 1 - kk.toNat + 1) kk.toNat (n - 1 - kk.toNat) (by lia)
          (by lia) (by lia) _
          (fun v => d.mul v ap.data[ap.off + ap.inc * (n * (n + 1) / 2 -
            (n - (n - 1 - kk.toNat)) * (n - (n - 1 - kk.toNat) + 1) / 2)]!), tpmvLowerStep]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [tpmvLowerG, Vec.idx_stride]
        by_cases h₁ : i = n - 1 - kk.toNat
        · simp only [h₁, ↓reduceIte, loIdx, Nat.sub_self, Nat.add_zero]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁),
            ite_eq_right_of_eq_false _ _ (eq_false h₁)]
          by_cases h₂ : n - 1 - kk.toNat < i
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
              ite_eq_left_of_eq_true _ _ (eq_true h₂), loIdx,
              show 1 + (i - (n - 1 - kk.toNat + 1)) = i - (n - 1 - kk.toNat) by lia]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia)),
              ite_eq_right_of_eq_false _ _ (eq_false h₂)]
      · intro l _ hl v
        have hl' := toNat_one_add_bandBelow (k := n) hn' hl
        have hq := toNat_packedLo_below hn hn' hjn hl
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, hp, hq.1, hl'.1, hj, getElem_eq_getElem!]
  · rfl

/--
Element `i` of `A * x` for the packed lower triangle `A`, on the arrays: `x[i] * A[i, i]`, or `x[i]`
for a unit diagonal, plus the terms `x[j] * A[i, j]` for `j = i - 1, …, 0`.
-/
@[expose] public def tpmvLower (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat) :
    Float :=
  Nat.fold i (fun t _ s =>
      s + x.data[x.off + x.inc * (i - 1 - t)]! * ap.data[ap.off + ap.inc * loIdx n (i - 1 - t) i]!)
    (d.mul x.data[x.off + x.inc * i]! ap.data[ap.off + ap.inc * loIdx n i i]!)

/-- The array of the lower product is the array of `x` with its elements multiplied. -/
public theorem tpmvLowerData_eq (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvLowerData d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpmvLower d ap x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tpmvLowerData_eq_iterRange]
  refine (iterRange_modifyAt_self x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun kk => n - 1 - kk) n (fun kk hkk => by lia)
    (fun kk => tpmvLowerG d ap (n - 1 - kk))).trans ?_
  rw [modifyAt_eq_read _ _ hinj (fun i _ hi => x.index_lt hi)]
  apply modifyAt_congr_fun
  intro i v _ hi
  have hread : ∀ kk, kk < n → selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
      (fun kk => tpmvLowerG d ap (n - 1 - kk)) kk = x.data[x.off + x.inc * (n - 1 - kk)]! :=
    fun kk _ => selfRead_eq_of_fix _ _ _ _ fun kk' hkk' t v => by
      simp only [tpmvLowerG]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia)),
        ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
  rw [show (fun kk (hkk : kk < n) v => tpmvLowerG d ap (n - 1 - kk)
        (selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
          (fun kk => tpmvLowerG d ap (n - 1 - kk)) kk) i v) =
      fun kk _ v => tpmvLowerG d ap (n - 1 - kk) x.data[x.off + x.inc * (n - 1 - kk)]! i v from by
    funext kk hkk v; rw [hread kk hkk]]
  simp only [tpmvLowerG]
  rw [fold_lower_tri_rev hi (fun j s => d.mul s ap.data[ap.off + ap.inc * loIdx n j j]!)
    (fun j s => s + x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * loIdx n j i]!),
    tpmvLower]
  rfl

/-! ## The transposed upper triangle -/

/--
The value that the step for column `j` of the transposed upper product writes at element `j`, from
the elements `get q` of `x`: `get j * A[j, j]`, or `get j` for a unit diagonal, plus the terms
`A[i, j] * get i` for `i = j - 1, …, 0`.
-/
@[expose] public def tpmvTUpperH (d : Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat)
    (get : Nat → Float) : Float :=
  Nat.fold j (fun t _ s => s + ap.data[ap.off + ap.inc * upIdx j (j - 1 - t)]! * get (j - 1 - t))
    (d.mul (get j) ap.data[ap.off + ap.inc * upIdx j j]!)

/-- The step `kk` of the transposed upper product, for the column `n - 1 - kk`. -/
@[expose] public def tpmvTUpperStep (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (kk : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n fun i v =>
    if i = n - 1 - kk then tpmvTUpperH d ap (n - 1 - kk) (fun q => c[x.stride.idx q]!) else v

/-- The array of the transposed upper product. -/
public def tpmvTUpperData (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Float64Array :=
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
        let v := a[o + c * (nu - 1 - kk)]
        have hd := toNat_packedUp_add hn hjn (l := nu - 1 - kk) (Nat.le_refl _)
        for t in 0...nu - 1 - kk with (s := d.mul v
            (ap.uget po pc rfl rfl hs.1 (packedUp (nu - 1 - kk) + (nu - 1 - kk)) (hd.1 ▸ hd.2))) do
          have ht : (nu - 1 - kk - 1 - t).toNat = n - 1 - kk.toNat - 1 - t.toNat := by grind
          have hp := toNat_packedUp_add hn hjn (l := nu - 1 - kk - 1 - t) (by lia)
          have hq' : (o + c * (nu - 1 - kk - 1 - t)).toNat < a.size :=
            x.toNat_index_lt hs.2 (by lia)
          s := s + ap.uget po pc rfl rfl hs.1 (packedUp (nu - 1 - kk) + (nu - 1 - kk - 1 - t))
            (hp.1 ▸ hp.2) * a[o + c * (nu - 1 - kk - 1 - t)]
        a[o + c * (nu - 1 - kk)] := s).2
  else iterRange (tpmvTUpperStep d ap x) 0 n x.data

public theorem tpmvTUpperData_eq_iterRange (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvTUpperData d ap x = iterRange (tpmvTUpperStep d ap x) 0 n x.data := by
  unfold tpmvTUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    have hF : ∀ j a, (tpmvTUpperStep d ap x j a).size = a.size := fun _ _ => by
      unfold tpmvTUpperStep; exact size_modifyAt _ _ _ _ _
    rw [Tail.run_forInFrom_unit (F := tpmvTUpperStep d ap x) (hF := hF)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro kk _ hkk next a h
      rw [hnu] at hkk
      have hj : (n.toUSize - 1 - kk).toNat = n - 1 - kk.toNat := by grind
      have hjn : (n.toUSize - 1 - kk).toNat < n := by lia
      have hd := toNat_packedUp_add hn hjn (l := n.toUSize - 1 - kk) (Nat.le_refl _)
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 + ap.data[ap.off + ap.inc * upIdx (n - 1 - kk.toNat) (n - 1 - kk.toNat - 1 - t)]! *
            p.2[x.off + x.inc * (n - 1 - kk.toNat - 1 - t)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, hj, iterRange_fst (fun t a s =>
          s + ap.data[ap.off + ap.inc * upIdx (n - 1 - kk.toNat) (n - 1 - kk.toNat - 1 - t)]! *
            a[x.off + x.inc * (n - 1 - kk.toNat - 1 - t)]!)]
        congr 1
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk)).toNat =
            x.off + x.inc * (n - 1 - kk.toNat) := by
          rw [x.toNat_index hs.2 hjn, hj]
        simp only [hp, Vec.uget_eq_getElem, Vec.getElem_def, hd.1, hj]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_eq_modifyAt_ite x a h (by lia), tpmvTUpperStep]
        rfl
      · intro t _ ht next' b a' h'
        rw [hj] at ht
        have ht' : (n.toUSize - 1 - kk - 1 - t).toNat = n - 1 - kk.toNat - 1 - t.toNat := by grind
        have hq := toNat_packedUp_add hn hjn (l := n.toUSize - 1 - kk - 1 - t) (by lia)
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk - 1 - t)).toNat =
            x.off + x.inc * (n - 1 - kk.toNat - 1 - t.toNat) := by
          rw [x.toNat_index hs.2 (by lia), ht']
        simp only [Tail.run_readThen, Vec.uget_eq_getElem, Vec.getElem_def, hp, hq.1, hj, ht',
          getElem_eq_getElem!, upIdx]
  · rfl

/--
Element `j` of `Aᵀ * x` for the packed upper triangle `A`, on the arrays: `x[j] * A[j, j]`, or
`x[j]` for a unit diagonal, plus the terms `A[i, j] * x[i]` for `i = j - 1, …, 0`.
-/
@[expose] public def tpmvTUpper (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) :
    Float :=
  tpmvTUpperH d ap j fun q => x.data[x.off + x.inc * q]!

/-- The array of the transposed upper product is the array of `x` with its elements multiplied. -/
public theorem tpmvTUpperData_eq (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvTUpperData d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpmvTUpper d ap x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tpmvTUpperData_eq_iterRange]
  refine (iterRange_write x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun kk => n - 1 - kk) (fun q => n - 1 - q) (fun kk hkk => by lia) (fun q hq => by lia)
    (fun kk => tpmvTUpperH d ap (n - 1 - kk)) (fun kk hkk get get' hget => by
      simp only [tpmvTUpperH]
      rw [hget _ (by lia)]
      congr 1
      funext t ht s
      rw [hget _ (by lia)]) (Nat.le_refl n)).trans ?_
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)), writeRead,
    show n - 1 - (n - 1 - i) = i by lia, tpmvTUpper, tpmvTUpperH, tpmvTUpperH,
    dite_eq_right (show ¬n - 1 - i < n - 1 - i by lia)]
  congr 1
  funext t ht s
  rw [dite_eq_right (show ¬n - 1 - (i - 1 - t) < n - 1 - i by lia)]
  rfl

/-! ## The transposed lower triangle -/

/--
The value that the step for column `j` of the transposed lower product writes at element `j`, from
the elements `get q` of `x`: `get j * A[j, j]`, or `get j` for a unit diagonal, plus the terms
`A[i, j] * get i` for `i = j + 1, …, n - 1`.
-/
@[expose] public def tpmvTLowerH (d : Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat)
    (get : Nat → Float) : Float :=
  Nat.fold (n - 1 - j) (fun t _ s =>
      s + ap.data[ap.off + ap.inc * loIdx n j (j + 1 + t)]! * get (j + 1 + t))
    (d.mul (get j) ap.data[ap.off + ap.inc * loIdx n j j]!)

/-- The step `j` of the transposed lower product. -/
@[expose] public def tpmvTLowerStep (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (j : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n fun i v =>
    if i = j then tpmvTLowerH d ap j (fun q => c[x.stride.idx q]!) else v

/-- The array of the transposed lower product. -/
public def tpmvTLowerData (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Float64Array :=
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
        let v := a[o + c * j]
        have hd := toNat_packedLo hn hjn
        for t in 0...nu - 1 - j with
            (s := d.mul v (ap.uget po pc rfl rfl hs.1 (packedLo n j) (hd.1 ▸ hd.2))) do
          have hc : (nu - 1 - j).toNat = n - 1 - j.toNat := by grind
          have ht : (1 + t).toNat = 1 + t.toNat := by grind
          have hp := toNat_packedLo_add hn hjn (l := 1 + t) (by lia)
          have hi : (j + 1 + t).toNat = j.toNat + 1 + t.toNat := by grind
          have hq' : (o + c * (j + 1 + t)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
          s := s + ap.uget po pc rfl rfl hs.1 (packedLo n j + (1 + t)) (hp.1 ▸ hp.2) *
            a[o + c * (j + 1 + t)]
        a[o + c * j] := s).2
  else iterRange (tpmvTLowerStep d ap x) 0 n x.data

public theorem tpmvTLowerData_eq_iterRange (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvTLowerData d ap x = iterRange (tpmvTLowerStep d ap x) 0 n x.data := by
  unfold tpmvTLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    have hF : ∀ j a, (tpmvTLowerStep d ap x j a).size = a.size := fun _ _ => by
      unfold tpmvTLowerStep; exact size_modifyAt _ _ _ _ _
    rw [Tail.run_forInFrom_unit (F := tpmvTLowerStep d ap x) (hF := hF)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hc : (n.toUSize - 1 - j).toNat = n - 1 - j.toNat := by grind
      have hd := toNat_packedLo hn hj
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 + ap.data[ap.off + ap.inc * loIdx n j.toNat (j.toNat + 1 + t)]! *
            p.2[x.off + x.inc * (j.toNat + 1 + t)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, hc, iterRange_fst (fun t a s =>
          s + ap.data[ap.off + ap.inc * loIdx n j.toNat (j.toNat + 1 + t)]! *
            a[x.off + x.inc * (j.toNat + 1 + t)]!)]
        congr 1
        have hp := x.toNat_index hs.2 hj
        simp only [hp, Vec.uget_eq_getElem, Vec.getElem_def, hd.1]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_eq_modifyAt_ite x a h hj, tpmvTLowerStep]
        simp only [tpmvTLowerH, loIdx, Nat.sub_self, Nat.add_zero, Vec.idx_stride]
      · intro t _ ht next' b a' h'
        rw [hc] at ht
        have ht' : (1 + t).toNat = 1 + t.toNat := by grind
        have hq := toNat_packedLo_add hn hj (l := 1 + t) (by lia)
        have hi : (j + 1 + t).toNat = j.toNat + 1 + t.toNat := by grind
        have hp : (x.off.toUSize + x.inc.toUSize * (j + 1 + t)).toNat =
            x.off + x.inc * (j.toNat + 1 + t.toNat) := by
          rw [x.toNat_index hs.2 (by lia), hi]
        simp only [Tail.run_readThen, Vec.uget_eq_getElem, Vec.getElem_def, hp, hq.1, ht',
          getElem_eq_getElem!, loIdx, show j.toNat + 1 + t.toNat - j.toNat = 1 + t.toNat by lia]
  · rfl

/--
Element `j` of `Aᵀ * x` for the packed lower triangle `A`, on the arrays: `x[j] * A[j, j]`, or
`x[j]` for a unit diagonal, plus the terms `A[i, j] * x[i]` for `i = j + 1, …, n - 1`.
-/
@[expose] public def tpmvTLower (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) :
    Float :=
  tpmvTLowerH d ap j fun q => x.data[x.off + x.inc * q]!

/-- The array of the transposed lower product is the array of `x` with its elements multiplied. -/
public theorem tpmvTLowerData_eq (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvTLowerData d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpmvTLower d ap x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tpmvTLowerData_eq_iterRange]
  refine (iterRange_write x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun j => j) (fun q => q) (fun j _ => rfl) (fun q _ => rfl)
    (fun j => tpmvTLowerH d ap j) (fun j hj get get' hget => by
      simp only [tpmvTLowerH]
      rw [hget _ hj]
      congr 1
      funext t ht s
      rw [hget _ (by lia)]) (Nat.le_refl n)).trans ?_
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi), writeRead, tpmvTLower, tpmvTLowerH, tpmvTLowerH,
    dite_eq_right (Nat.lt_irrefl i)]
  congr 1
  funext t ht s
  rw [dite_eq_right (show ¬i + 1 + t < i by lia)]
  rfl

/-! ## `tpmv` and `tpmvT` -/

/-- The product `A * x` for the packed triangle `uplo` `A`, element by element. -/
@[expose] public def tpmvProd (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => tpmvUpper d ap x
  | .lower => tpmvLower d ap x

/-- The array of `tpmv`. -/
@[expose] public def tpmvData (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Float64Array :=
  match uplo with
  | .upper => tpmvUpperData d ap x
  | .lower => tpmvLowerData d ap x

public theorem tpmvData_eq (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvData uplo d ap x = x.data.modifyAt x.stride.idx 0 n fun i _ => tpmvProd uplo d ap x i := by
  cases uplo
  · exact tpmvUpperData_eq d ap x
  · exact tpmvLowerData_eq d ap x

/--
`tpmv uplo d ap x` is `A * x` for the triangular matrix `A` whose triangle `uplo` is packed in `ap`,
with a unit diagonal if `d` is `.unit`, by the column-oriented loops of the reference BLAS (`dtpmv`
with `TRANS = 'N'`). For the upper triangle, it adds `x[j]` times column `j` to the elements above
`j` and multiplies element `j` by the diagonal, for `j = 0, …, n - 1`; for the lower triangle, it
does the same from `j = n - 1` down to `0`, with the elements below. It updates `x` in place when
its array is not shared, leaves the elements of the array outside `x` unchanged, and does not read
the diagonal when `d` is `.unit`.
-/
@[expose] public def tpmv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Vec n where
  data := tpmvData uplo d ap x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [tpmvData_eq, size_modifyAt]; exact x.bound

/-- The array of `tpmv uplo d ap x` is the array of `x` with its elements multiplied. -/
public theorem data_tpmv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    (tpmv uplo d ap x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => tpmvProd uplo d ap x i :=
  tpmvData_eq uplo d ap x

@[simp] public theorem off_tpmv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    (tpmv uplo d ap x).off = x.off := rfl

@[simp] public theorem inc_tpmv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    (tpmv uplo d ap x).inc = x.inc := rfl

/-- Element `i` of `tpmv uplo d ap x` is element `i` of the model. -/
public theorem getElem_tpmv (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) (h : i < n) : (tpmv uplo d ap x)[i] = tpmvProd uplo d ap x i :=
  Vec.getElem_of_data_eq_modifyAt _ (data_tpmv uplo d ap x) rfl rfl i h

/--
Element `i` of `tpmv .upper d ap x` is `x[i] * A[i, i]`, or `x[i]` for a unit diagonal, plus the
terms `x[i + 1 + t] * A[i, i + 1 + t]` for `t < n - 1 - i`, where `A[i, j]` is `ap[upIdx j i]`.
-/
public theorem getElem_tpmv_upper (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat)
    (h : i < n) :
    (tpmv .upper d ap x)[i] = Nat.fold (n - 1 - i) (fun t _ s =>
      s + x[i + 1 + t]'(by lia) * ap[upIdx (i + 1 + t) i]'(upIdx_lt (by lia) (by lia)))
      (d.mul x[i] (ap[upIdx i i]'(upIdx_lt (Nat.le_refl i) h))) := by
  rw [getElem_tpmv _ _ _ _ _ h, tpmvProd, tpmvUpper, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (Nat.le_refl i) h))]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)),
    getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (by lia) (by lia)))]
  rfl

/--
Element `i` of `tpmv .lower d ap x` is `x[i] * A[i, i]`, or `x[i]` for a unit diagonal, plus the
terms `x[i - 1 - t] * A[i, i - 1 - t]` for `t < i`, where `A[i, j]` is `ap[loIdx n j i]`.
-/
public theorem getElem_tpmv_lower (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat)
    (h : i < n) :
    (tpmv .lower d ap x)[i] = Nat.fold i (fun t _ s =>
      s + x[i - 1 - t]'(by lia) * ap[loIdx n (i - 1 - t) i]'(loIdx_lt (by lia) h))
      (d.mul x[i] (ap[loIdx n i i]'(loIdx_lt (Nat.le_refl i) h))) := by
  rw [getElem_tpmv _ _ _ _ _ h, tpmvProd, tpmvLower, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (Nat.le_refl i) h))]
  congr 1
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)),
    getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (by lia) h))]
  rfl

/-- The product `Aᵀ * x` for the packed triangle `uplo` `A`, element by element. -/
@[expose] public def tpmvTProd (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => tpmvTUpper d ap x
  | .lower => tpmvTLower d ap x

/-- The array of `tpmvT`. -/
@[expose] public def tpmvTData (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Float64Array :=
  match uplo with
  | .upper => tpmvTUpperData d ap x
  | .lower => tpmvTLowerData d ap x

public theorem tpmvTData_eq (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    tpmvTData uplo d ap x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tpmvTProd uplo d ap x i := by
  cases uplo
  · exact tpmvTUpperData_eq d ap x
  · exact tpmvTLowerData_eq d ap x

/--
`tpmvT uplo d ap x` is `Aᵀ * x` for the triangular matrix `A` whose triangle `uplo` is packed in
`ap`, with a unit diagonal if `d` is `.unit`, by the loops of the reference BLAS (`dtpmv` with
`TRANS = 'T'`). For the upper triangle, it sets element `j` to its diagonal term plus the dot
product of column `j` above the diagonal, from the diagonal up, and of `x`, for `j = n - 1` down to
`0`; for the lower triangle, it does the same for `j = 0, …, n - 1`, with the column below the
diagonal, from the diagonal down. It updates `x` in place when its array is not shared, leaves the
elements of the array outside `x` unchanged, and does not read the diagonal when `d` is `.unit`.
-/
@[expose] public def tpmvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Vec n where
  data := tpmvTData uplo d ap x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [tpmvTData_eq, size_modifyAt]; exact x.bound

/-- The array of `tpmvT uplo d ap x` is the array of `x` with its elements multiplied. -/
public theorem data_tpmvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    (tpmvT uplo d ap x).data =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tpmvTProd uplo d ap x i :=
  tpmvTData_eq uplo d ap x

@[simp] public theorem off_tpmvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : (tpmvT uplo d ap x).off = x.off := rfl

@[simp] public theorem inc_tpmvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : (tpmvT uplo d ap x).inc = x.inc := rfl

/-- Element `j` of `tpmvT uplo d ap x` is element `j` of the model. -/
public theorem getElem_tpmvT (uplo : Uplo) (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (j : Nat) (h : j < n) : (tpmvT uplo d ap x)[j] = tpmvTProd uplo d ap x j :=
  Vec.getElem_of_data_eq_modifyAt _ (data_tpmvT uplo d ap x) rfl rfl j h

/--
Element `j` of `tpmvT .upper d ap x` is `x[j] * A[j, j]`, or `x[j]` for a unit diagonal, plus the
terms `A[j - 1 - t, j] * x[j - 1 - t]` for `t < j`, where `A[i, j]` is `ap[upIdx j i]`.
-/
public theorem getElem_tpmvT_upper (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat)
    (h : j < n) :
    (tpmvT .upper d ap x)[j] = Nat.fold j (fun t _ s =>
      s + ap[upIdx j (j - 1 - t)]'(upIdx_lt (by lia) h) * x[j - 1 - t]'(by lia))
      (d.mul x[j] (ap[upIdx j j]'(upIdx_lt (Nat.le_refl j) h))) := by
  rw [getElem_tpmvT _ _ _ _ _ h, tpmvTProd, tpmvTUpper, tpmvTUpperH,
    getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (Nat.le_refl j) h))]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)),
    getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (by lia) h))]
  rfl

/--
Element `j` of `tpmvT .lower d ap x` is `x[j] * A[j, j]`, or `x[j]` for a unit diagonal, plus the
terms `A[j + 1 + t, j] * x[j + 1 + t]` for `t < n - 1 - j`, where `A[i, j]` is `ap[loIdx n j i]`.
-/
public theorem getElem_tpmvT_lower (d : Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat)
    (h : j < n) :
    (tpmvT .lower d ap x)[j] = Nat.fold (n - 1 - j) (fun t _ s =>
      s + ap[loIdx n j (j + 1 + t)]'(loIdx_lt (by lia) (by lia)) * x[j + 1 + t]'(by lia))
      (d.mul x[j] (ap[loIdx n j j]'(loIdx_lt (Nat.le_refl j) h))) := by
  rw [getElem_tpmvT _ _ _ _ _ h, tpmvTProd, tpmvTLower, tpmvTLowerH,
    getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (Nat.le_refl j) h))]
  congr 1
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)),
    getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (by lia) (by lia)))]
  rfl

end Mat

end BLAS.Float64
