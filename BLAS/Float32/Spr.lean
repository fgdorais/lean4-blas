/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Packed
public import BLAS.Float32.Syrk
import all BLAS.Internal

/-!
# Packed symmetric rank-one and rank-two updates

`Mat.spr uplo α x ap` computes `α * x * xᵀ + A` and `Mat.spr2 uplo α x y ap` computes
`α * x * yᵀ + α * y * xᵀ + A`, for the symmetric matrix `A` whose triangle `uplo` is packed in `ap`
as for `Mat.tpmv`, by the loops of the reference BLAS (`dspr` and `dspr2`), as `Mat.syr` and
`Mat.syr2` do for a full matrix. As there, they return `ap` when `α = 0`, and skip the columns `j`
with `x[j] = 0` (with `x[j] = y[j] = 0` for `spr2`), so that an infinity or a `NaN` elsewhere in
`x` or `y` doesn't reach them. They update `ap` in place when its array is not shared, and leave the
elements of the array outside `ap` unchanged.

Column `j` of the packed triangle is the elements `packedStart uplo n j + l` of `ap` for
`l < packedLen uplo n j`, which hold the rows `packedRow uplo j + l`.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

/-- The index in `ap` of the first element of column `j` of a packed triangle of order `n`. -/
@[expose] public def packedStart (uplo : Uplo) (n j : Nat) : Nat :=
  match uplo with
  | .upper => j * (j + 1) / 2
  | .lower => n * (n + 1) / 2 - (n - j) * (n - j + 1) / 2

/-- The number of elements of column `j` of a packed triangle of order `n`. -/
@[expose] public def packedLen (uplo : Uplo) (n j : Nat) : Nat :=
  match uplo with
  | .upper => j + 1
  | .lower => n - j

/-- The row of the first element of column `j` of a packed triangle. -/
@[expose] public def packedRow (uplo : Uplo) (j : Nat) : Nat :=
  match uplo with
  | .upper => 0
  | .lower => j

namespace Mat

variable {n : Nat}

/-- The `USize` index `j + l` of a row of column `j` below the diagonal. -/
private theorem toNat_add_lt {j l : USize} (hn : n < USize.size) (hl : l.toNat < n - j.toNat) :
    (j + l).toNat = j.toNat + l.toNat ∧ j.toNat + l.toNat < n := by
  constructor
  · rw [USize.toNat_add, Nat.mod_eq_of_lt (by lia)]
  · lia

/-- The `USize` value `j + 1`, for `j < n`. -/
private theorem toNat_succ_lt {j : USize} (hn : n < USize.size) (hj : j.toNat < n) :
    (j + 1).toNat = j.toNat + 1 := by
  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by lia)]

/-- The `USize` value `n - j`, for `j < n`. -/
private theorem toNat_sub_lt {j : USize} (hn : n < USize.size) (hj : j.toNat < n) :
    (n.toUSize - j).toNat = n - j.toNat := by
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, USize.toNat_ofNat_of_lt' hn]; lia),
    USize.toNat_ofNat_of_lt' hn]

/-- The number of elements that the loops update in column `j`: none when the column is skipped. -/
private theorem toNat_syrkRows_zero {hi : USize} (b : Bool) :
    (syrkRows 0 hi b).toNat = if b then 0 else hi.toNat := by
  unfold syrkRows; split <;> simp

/-- Element `p` of `ap` is in the column `j` of the packed triangle. -/
private theorem packedStart_unique {uplo : Uplo} {j j' p : Nat} (hj : j < n) (hj' : j' < n)
    (hp : packedStart uplo n j ≤ p) (hp' : p < packedStart uplo n j + packedLen uplo n j)
    (hq : packedStart uplo n j' ≤ p) (hq' : p < packedStart uplo n j' + packedLen uplo n j') :
    j' = j := by
  cases uplo
  · exact packedUp_col_unique hp hp' hq hq'
  · exact packedLo_col_unique hj hj' hp hp' hq hq'

/-! ## The columns -/

/--
The map of column `j` of the loops of `spr` on element `p` of `ap`: add `x[r] * (α * x[j])` to the
element of row `r` of the column, unless `x[j] = 0`.
-/
@[expose] public def sprCol (uplo : Uplo) (α : Float32) (x : Vec n) (j p : Nat) (v : Float32) :
    Float32 :=
  if packedStart uplo n j ≤ p ∧ p < packedStart uplo n j +
      (if x.data[x.off + x.inc * j]! == 0 then 0 else packedLen uplo n j) then
    v + x.data[x.off + x.inc * (packedRow uplo j + (p - packedStart uplo n j))]! *
      (α * x.data[x.off + x.inc * j]!)
  else v

/-- The value of the loops of `spr` at element `p` of `ap`, from its old value `v`. -/
@[expose] public def sprAt (uplo : Uplo) (α : Float32) (x : Vec n) (p : Nat) (v : Float32) :
    Float32 :=
  Nat.fold n (fun j _ v => sprCol uplo α x j p v) v

/-- The array of `spr` for the upper triangle. -/
public def sprUpperData (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) : Float32Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    let a := ap.data
    let po := ap.off.toUSize
    let pc := ap.inc.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    (inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        let xj := x.uget xo xc rfl rfl hs.2 j hjn
        let t := α * xj
        -- A skipped column runs an empty loop: an `if` would allocate a closure per column.
        let cnt := syrkRows 0 (j + 1) (xj == 0)
        have hh : cnt.toNat ≤ j.toNat + 1 := by
          rw [toNat_syrkRows_zero, toNat_succ_lt hn' hjn]; split <;> lia
        for l in 0...cnt do
          have hl : l.toNat ≤ j.toNat := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (by assumption) hh)
          have hp := toNat_packedUp_add hn hjn hl
          have hq : (po + pc * (packedUp j + l)).toNat < a.size :=
            ap.toNat_index_lt hs.1 (hp.1 ▸ hp.2)
          a[po + pc * (packedUp j + l)] := a[po + pc * (packedUp j + l)] +
            x.uget xo xc rfl rfl hs.2 l (Nat.lt_of_le_of_lt hl hjn) * t).2
  else iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (sprCol .upper α x j))
    0 n ap.data

/-- The array of `spr` for the lower triangle. -/
public def sprLowerData (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) : Float32Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    let a := ap.data
    let po := ap.off.toUSize
    let pc := ap.inc.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    (inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        let xj := x.uget xo xc rfl rfl hs.2 j hjn
        let t := α * xj
        let cnt := syrkRows 0 (nu - j) (xj == 0)
        have hh : cnt.toNat ≤ n - j.toNat := by
          rw [toNat_syrkRows_zero, toNat_sub_lt hn' hjn]; split <;> lia
        for l in 0...cnt do
          have hl : l.toNat < n - j.toNat := Nat.lt_of_lt_of_le (by assumption) hh
          have hp := toNat_packedLo_add hn hjn hl
          have hi := toNat_add_lt hn' hl
          have hq : (po + pc * (packedLo n j + l)).toNat < a.size :=
            ap.toNat_index_lt hs.1 (hp.1 ▸ hp.2)
          a[po + pc * (packedLo n j + l)] := a[po + pc * (packedLo n j + l)] +
            x.uget xo xc rfl rfl hs.2 (j + l) (hi.1 ▸ hi.2) * t).2
  else iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (sprCol .lower α x j))
    0 n ap.data

public theorem sprUpperData_eq (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    sprUpperData α x ap =
      iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (sprCol .upper α x j))
        0 n ap.data := by
  unfold sprUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (sprCol .upper α x j)) (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hy := getElem!_pos x.data (x.off + x.inc * j.toNat) (x.index_lt hj)
      have hc : ∀ b : Bool, (syrkRows 0 (j + 1) b).toNat = if b then 0 else j.toNat + 1 := by
        intro b; rw [toNat_syrkRows_zero, toNat_succ_lt hn' hj]
      have hle : ∀ (b : Bool) (l : USize), l.toNat < (syrkRows 0 (j + 1) b).toNat →
          l.toNat ≤ j.toNat := fun b l hl => by rw [hc] at hl; split at hl <;> lia
      rw [Tail.run_forInFrom_modify
        (e := fun l => ap.off.toUSize + ap.inc.toUSize * (packedUp j + l))
        (idx := fun l => ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + l))
        (he := fun l _ hl => by
          have hp := toNat_packedUp_add hn hj (hle _ l hl)
          rw [ap.toNat_index hs.1 (hp.1 ▸ hp.2), hp.1])
        (G := fun l v => v + x.data[x.off + x.inc * l]! * (α * x.data[x.off + x.inc * j.toNat]!))]
      · apply run_congr
        simp only [USize.toNat_zero, hc, Vec.uget_eq_getElem, Vec.getElem_def, ← hy]
        rw [modifyAt_band ap a _ _ (by split <;> have := tri_upper_lt (Nat.le_refl _) hj <;> lia)]
        apply modifyAt_congr_fun
        intro p v _ _
        simp only [sprCol, packedStart, packedLen, packedRow, Nat.zero_add]
      · intro l _ hl v
        have hl' := hle _ l hl
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, ← hy,
          getElem!_pos x.data (x.off + x.inc * l.toNat) (x.index_lt (by lia))]
  · rfl

public theorem sprLowerData_eq (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    sprLowerData α x ap =
      iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (sprCol .lower α x j))
        0 n ap.data := by
  unfold sprLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (sprCol .lower α x j)) (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hy := getElem!_pos x.data (x.off + x.inc * j.toNat) (x.index_lt hj)
      have hc : ∀ b : Bool, (syrkRows 0 (n.toUSize - j) b).toNat = if b then 0 else n - j.toNat :=
        by intro b; rw [toNat_syrkRows_zero, toNat_sub_lt hn' hj]
      have hle : ∀ (b : Bool) (l : USize), l.toNat < (syrkRows 0 (n.toUSize - j) b).toNat →
          l.toNat < n - j.toNat := fun b l hl => by rw [hc] at hl; split at hl <;> lia
      rw [Tail.run_forInFrom_modify
        (e := fun l => ap.off.toUSize + ap.inc.toUSize * (packedLo n j + l))
        (idx := fun l => ap.off + ap.inc *
          (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + l))
        (he := fun l _ hl => by
          have hp := toNat_packedLo_add hn hj (hle _ l hl)
          rw [ap.toNat_index hs.1 (hp.1 ▸ hp.2), hp.1])
        (G := fun l v => v + x.data[x.off + x.inc * (j.toNat + l)]! *
          (α * x.data[x.off + x.inc * j.toNat]!))]
      · apply run_congr
        simp only [USize.toNat_zero, hc, Vec.uget_eq_getElem, Vec.getElem_def, ← hy]
        rw [modifyAt_band ap a _ _ (by
          split
          · lia
          · have := tri_lower_lt (i := n - 1) (j := j.toNat) (n := n) (by lia) (by lia)
            lia)]
        apply modifyAt_congr_fun
        intro p v _ _
        simp only [sprCol, packedStart, packedLen, packedRow]
        rfl
      · intro l _ hl v
        have hi := toNat_add_lt hn' (hle _ l hl)
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, ← hy, hi.1,
          getElem!_pos x.data (x.off + x.inc * (j.toNat + l.toNat)) (x.index_lt hi.2)]
  · rfl

/-- The array of the loops of `spr`. -/
@[expose] public def sprData (uplo : Uplo) (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    Float32Array :=
  match uplo with
  | .upper => sprUpperData α x ap
  | .lower => sprLowerData α x ap

public theorem sprData_eq (uplo : Uplo) (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    sprData uplo α x ap = ap.data.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (sprAt uplo α x) := by
  have hinj := ap.fits.injOn (lo := 0) (Nat.le_refl _)
  have e : sprData uplo α x ap =
      iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (sprCol uplo α x j))
        0 n ap.data := by
    cases uplo
    · exact sprUpperData_eq α x ap
    · exact sprLowerData_eq α x ap
  rw [e, iterRange_modifyAt _ _ hinj]
  rfl

/-! ## `spr` -/

/--
`spr uplo α x ap` is `α * x * xᵀ + A` for the symmetric matrix `A` whose triangle `uplo` is packed
in `ap`, by the loops of the reference BLAS (`dspr`): for each column `j`, it adds `x` times
`α * x[j]` to the column of the triangle. As in the reference BLAS, it returns `ap` when `α = 0`,
and skips the columns with `x[j] = 0`. It updates `ap` in place when its array is not shared, and
leaves the elements of the array outside `ap` unchanged.
-/
@[expose] public def spr (uplo : Uplo) (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    Vec (n * (n + 1) / 2) :=
  if α == 0 then ap
  else
    { data := sprData uplo α x ap
      off := ap.off
      inc := ap.inc
      inc_pos := ap.inc_pos
      bound := by rw [sprData_eq, size_modifyAt]; exact ap.bound }

public theorem data_spr (uplo : Uplo) (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    (spr uplo α x ap).data = ap.data.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) fun p v =>
      if α == 0 then v else sprAt uplo α x p v := by
  unfold spr
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, sprData_eq]
  · simp only [↓reduceIte]
    exact (modifyAt_id _ _ _ _).symm

@[simp] public theorem off_spr (uplo : Uplo) (α : Float32) (x : Vec n)
    (ap : Vec (n * (n + 1) / 2)) : (spr uplo α x ap).off = ap.off := by
  unfold spr; split <;> rfl

@[simp] public theorem inc_spr (uplo : Uplo) (α : Float32) (x : Vec n)
    (ap : Vec (n * (n + 1) / 2)) : (spr uplo α x ap).inc = ap.inc := by
  unfold spr; split <;> rfl

/-- Element `p` of `spr uplo α x ap` is `ap[p]` when `α = 0`, and `sprAt` of it otherwise. -/
public theorem getElem_spr (uplo : Uplo) (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2))
    (p : Nat) (h : p < n * (n + 1) / 2) :
    (spr uplo α x ap)[p] = if α == 0 then ap[p] else sprAt uplo α x p ap[p] :=
  Vec.getElem_of_data_eq_modifyAt _ (data_spr uplo α x ap) (off_spr uplo α x ap)
    (inc_spr uplo α x ap) p h

/-- Column `j` of the loops of `spr` is the only one that updates the element `i` of column `j`. -/
private theorem sprAt_col (uplo : Uplo) (α : Float32) (x : Vec n) {i j : Nat} (hj : j < n)
    (hi : packedRow uplo j ≤ i) (hi' : i < packedRow uplo j + packedLen uplo n j) (v : Float32) :
    sprAt uplo α x (packedStart uplo n j + (i - packedRow uplo j)) v =
      if x.data[x.off + x.inc * j]! == 0 then v
      else v + x.data[x.off + x.inc * i]! * (α * x.data[x.off + x.inc * j]!) := by
  rw [sprAt, fold_single hj (fun j' v => sprCol uplo α x j'
    (packedStart uplo n j + (i - packedRow uplo j)) v)]
  · unfold sprCol
    cases x.data[x.off + x.inc * j]! == 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
        show packedRow uplo j + (packedStart uplo n j + (i - packedRow uplo j) -
          packedStart uplo n j) = i by lia]
    · simp only [↓reduceIte]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
  · intro j' hj' hne v
    unfold sprCol
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun ⟨h₁, h₂⟩ => hne
      (packedStart_unique hj hj' (Nat.le_add_right _ _) (by lia) h₁ (by split at h₂ <;> lia)))]

/--
Element `(i, j)` of the packed upper triangle of `spr .upper α x ap`, for `i ≤ j`, is
`ap[upIdx j i]` when `α = 0` or `x[j] = 0`, and `ap[upIdx j i] + x[i] * (α * x[j])` otherwise.
-/
public theorem getElem_spr_upper (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) {i j : Nat}
    (hij : i ≤ j) (hj : j < n) :
    (spr .upper α x ap)[upIdx j i]'(upIdx_lt hij hj) =
      if α == 0 || x[j] == 0 then ap[upIdx j i]'(upIdx_lt hij hj)
      else ap[upIdx j i]'(upIdx_lt hij hj) + x[i]'(by lia) * (α * x[j]) := by
  rw [getElem_spr]
  have e : sprAt .upper α x (upIdx j i) (ap[upIdx j i]'(upIdx_lt hij hj)) = _ :=
    sprAt_col .upper α x hj (Nat.zero_le i) (show i < 0 + (j + 1) by lia) _
  rw [e,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt (by lia)),
    getElem!_pos x.data (x.off + x.inc * j) (x.index_lt hj)]
  cases α == 0 <;> cases x[j] == 0 <;> rfl

/--
Element `(i, j)` of the packed lower triangle of `spr .lower α x ap`, for `i ≥ j`, is
`ap[loIdx n j i]` when `α = 0` or `x[j] = 0`, and `ap[loIdx n j i] + x[i] * (α * x[j])` otherwise.
-/
public theorem getElem_spr_lower (α : Float32) (x : Vec n) (ap : Vec (n * (n + 1) / 2)) {i j : Nat}
    (hji : j ≤ i) (hi : i < n) :
    (spr .lower α x ap)[loIdx n j i]'(loIdx_lt hji hi) =
      if α == 0 || x[j] == 0 then ap[loIdx n j i]'(loIdx_lt hji hi)
      else ap[loIdx n j i]'(loIdx_lt hji hi) + x[i] * (α * x[j]'(by lia)) := by
  rw [getElem_spr]
  have e : sprAt .lower α x (loIdx n j i) (ap[loIdx n j i]'(loIdx_lt hji hi)) = _ :=
    sprAt_col .lower α x (i := i) (j := j) (by lia) hji (show i < j + (n - j) by lia) _
  rw [e,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt hi),
    getElem!_pos x.data (x.off + x.inc * j) (x.index_lt (by lia))]
  cases α == 0 <;> cases x[j] == 0 <;> rfl

/-! ## `spr2` -/

/--
The map of column `j` of the loops of `spr2` on element `p` of `ap`: add
`x[r] * (α * y[j]) + y[r] * (α * x[j])` to the element of row `r` of the column, unless
`x[j] = y[j] = 0`.
-/
@[expose] public def spr2Col (uplo : Uplo) (α : Float32) (x y : Vec n) (j p : Nat) (v : Float32) :
    Float32 :=
  if packedStart uplo n j ≤ p ∧ p < packedStart uplo n j +
      (if x.data[x.off + x.inc * j]! == 0 && y.data[y.off + y.inc * j]! == 0 then 0
        else packedLen uplo n j) then
    v + x.data[x.off + x.inc * (packedRow uplo j + (p - packedStart uplo n j))]! *
        (α * y.data[y.off + y.inc * j]!) +
      y.data[y.off + y.inc * (packedRow uplo j + (p - packedStart uplo n j))]! *
        (α * x.data[x.off + x.inc * j]!)
  else v

/-- The value of the loops of `spr2` at element `p` of `ap`, from its old value `v`. -/
@[expose] public def spr2At (uplo : Uplo) (α : Float32) (x y : Vec n) (p : Nat) (v : Float32) :
    Float32 :=
  Nat.fold n (fun j _ v => spr2Col uplo α x y j p v) v

/-- The array of `spr2` for the upper triangle. -/
public def spr2UpperData (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2)) : Float32Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2.1
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
    let a := ap.data
    let po := ap.off.toUSize
    let pc := ap.inc.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    let yo := y.off.toUSize
    let yc := y.inc.toUSize
    (inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        let xj := x.uget xo xc rfl rfl hs.2.1 j hjn
        let yj := y.uget yo yc rfl rfl hs.2.2 j hjn
        let t1 := α * yj
        let t2 := α * xj
        let cnt := syrkRows 0 (j + 1) (xj == 0 && yj == 0)
        have hh : cnt.toNat ≤ j.toNat + 1 := by
          rw [toNat_syrkRows_zero, toNat_succ_lt hn' hjn]; split <;> lia
        for l in 0...cnt do
          have hl : l.toNat ≤ j.toNat := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (by assumption) hh)
          have hp := toNat_packedUp_add hn hjn hl
          have hq : (po + pc * (packedUp j + l)).toNat < a.size :=
            ap.toNat_index_lt hs.1 (hp.1 ▸ hp.2)
          a[po + pc * (packedUp j + l)] := a[po + pc * (packedUp j + l)] +
            x.uget xo xc rfl rfl hs.2.1 l (Nat.lt_of_le_of_lt hl hjn) * t1 +
            y.uget yo yc rfl rfl hs.2.2 l (Nat.lt_of_le_of_lt hl hjn) * t2).2
  else iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (spr2Col .upper α x y j))
    0 n ap.data

/-- The array of `spr2` for the lower triangle. -/
public def spr2LowerData (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2)) : Float32Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2.1
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
    let a := ap.data
    let po := ap.off.toUSize
    let pc := ap.inc.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    let yo := y.off.toUSize
    let yc := y.inc.toUSize
    (inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        let xj := x.uget xo xc rfl rfl hs.2.1 j hjn
        let yj := y.uget yo yc rfl rfl hs.2.2 j hjn
        let t1 := α * yj
        let t2 := α * xj
        let cnt := syrkRows 0 (nu - j) (xj == 0 && yj == 0)
        have hh : cnt.toNat ≤ n - j.toNat := by
          rw [toNat_syrkRows_zero, toNat_sub_lt hn' hjn]; split <;> lia
        for l in 0...cnt do
          have hl : l.toNat < n - j.toNat := Nat.lt_of_lt_of_le (by assumption) hh
          have hp := toNat_packedLo_add hn hjn hl
          have hi := toNat_add_lt hn' hl
          have hq : (po + pc * (packedLo n j + l)).toNat < a.size :=
            ap.toNat_index_lt hs.1 (hp.1 ▸ hp.2)
          a[po + pc * (packedLo n j + l)] := a[po + pc * (packedLo n j + l)] +
            x.uget xo xc rfl rfl hs.2.1 (j + l) (hi.1 ▸ hi.2) * t1 +
            y.uget yo yc rfl rfl hs.2.2 (j + l) (hi.1 ▸ hi.2) * t2).2
  else iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (spr2Col .lower α x y j))
    0 n ap.data

public theorem spr2UpperData_eq (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    spr2UpperData α x y ap =
      iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (spr2Col .upper α x y j))
        0 n ap.data := by
  unfold spr2UpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2.1
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (spr2Col .upper α x y j)) (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hx := getElem!_pos x.data (x.off + x.inc * j.toNat) (x.index_lt hj)
      have hy := getElem!_pos y.data (y.off + y.inc * j.toNat) (y.index_lt hj)
      have hc : ∀ b : Bool, (syrkRows 0 (j + 1) b).toNat = if b then 0 else j.toNat + 1 := by
        intro b; rw [toNat_syrkRows_zero, toNat_succ_lt hn' hj]
      have hle : ∀ (b : Bool) (l : USize), l.toNat < (syrkRows 0 (j + 1) b).toNat →
          l.toNat ≤ j.toNat := fun b l hl => by rw [hc] at hl; split at hl <;> lia
      rw [Tail.run_forInFrom_modify
        (e := fun l => ap.off.toUSize + ap.inc.toUSize * (packedUp j + l))
        (idx := fun l => ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + l))
        (he := fun l _ hl => by
          have hp := toNat_packedUp_add hn hj (hle _ l hl)
          rw [ap.toNat_index hs.1 (hp.1 ▸ hp.2), hp.1])
        (G := fun l v => v + x.data[x.off + x.inc * l]! * (α * y.data[y.off + y.inc * j.toNat]!) +
          y.data[y.off + y.inc * l]! * (α * x.data[x.off + x.inc * j.toNat]!))]
      · apply run_congr
        simp only [USize.toNat_zero, hc, Vec.uget_eq_getElem, Vec.getElem_def, ← hx, ← hy]
        rw [modifyAt_band ap a _ _ (by split <;> have := tri_upper_lt (Nat.le_refl _) hj <;> lia)]
        apply modifyAt_congr_fun
        intro p v _ _
        simp only [spr2Col, packedStart, packedLen, packedRow, Nat.zero_add]
      · intro l _ hl v
        have hl' := hle _ l hl
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, ← hx, ← hy,
          getElem!_pos x.data (x.off + x.inc * l.toNat) (x.index_lt (by lia)),
          getElem!_pos y.data (y.off + y.inc * l.toNat) (y.index_lt (by lia))]
  · rfl

public theorem spr2LowerData_eq (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    spr2LowerData α x y ap =
      iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (spr2Col .lower α x y j))
        0 n ap.data := by
  unfold spr2LowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2.1
    have hn := tri_lt_size ap hs.1
    have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (spr2Col .lower α x y j)) (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hx := getElem!_pos x.data (x.off + x.inc * j.toNat) (x.index_lt hj)
      have hy := getElem!_pos y.data (y.off + y.inc * j.toNat) (y.index_lt hj)
      have hc : ∀ b : Bool, (syrkRows 0 (n.toUSize - j) b).toNat = if b then 0 else n - j.toNat :=
        by intro b; rw [toNat_syrkRows_zero, toNat_sub_lt hn' hj]
      have hle : ∀ (b : Bool) (l : USize), l.toNat < (syrkRows 0 (n.toUSize - j) b).toNat →
          l.toNat < n - j.toNat := fun b l hl => by rw [hc] at hl; split at hl <;> lia
      rw [Tail.run_forInFrom_modify
        (e := fun l => ap.off.toUSize + ap.inc.toUSize * (packedLo n j + l))
        (idx := fun l => ap.off + ap.inc *
          (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + l))
        (he := fun l _ hl => by
          have hp := toNat_packedLo_add hn hj (hle _ l hl)
          rw [ap.toNat_index hs.1 (hp.1 ▸ hp.2), hp.1])
        (G := fun l v => v + x.data[x.off + x.inc * (j.toNat + l)]! *
            (α * y.data[y.off + y.inc * j.toNat]!) +
          y.data[y.off + y.inc * (j.toNat + l)]! * (α * x.data[x.off + x.inc * j.toNat]!))]
      · apply run_congr
        simp only [USize.toNat_zero, hc, Vec.uget_eq_getElem, Vec.getElem_def, ← hx, ← hy]
        rw [modifyAt_band ap a _ _ (by
          split
          · lia
          · have := tri_lower_lt (i := n - 1) (j := j.toNat) (n := n) (by lia) (by lia)
            lia)]
        apply modifyAt_congr_fun
        intro p v _ _
        simp only [spr2Col, packedStart, packedLen, packedRow]
        rfl
      · intro l _ hl v
        have hi := toNat_add_lt hn' (hle _ l hl)
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, ← hx, ← hy, hi.1,
          getElem!_pos x.data (x.off + x.inc * (j.toNat + l.toNat)) (x.index_lt hi.2),
          getElem!_pos y.data (y.off + y.inc * (j.toNat + l.toNat)) (y.index_lt hi.2)]
  · rfl

/-- The array of the loops of `spr2`. -/
@[expose] public def spr2Data (uplo : Uplo) (α : Float32) (x y : Vec n)
    (ap : Vec (n * (n + 1) / 2)) : Float32Array :=
  match uplo with
  | .upper => spr2UpperData α x y ap
  | .lower => spr2LowerData α x y ap

public theorem spr2Data_eq (uplo : Uplo) (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    spr2Data uplo α x y ap =
      ap.data.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (spr2At uplo α x y) := by
  have hinj := ap.fits.injOn (lo := 0) (Nat.le_refl _)
  have e : spr2Data uplo α x y ap =
      iterRange (fun j c => c.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) (spr2Col uplo α x y j))
        0 n ap.data := by
    cases uplo
    · exact spr2UpperData_eq α x y ap
    · exact spr2LowerData_eq α x y ap
  rw [e, iterRange_modifyAt _ _ hinj]
  rfl

/--
`spr2 uplo α x y ap` is `α * x * yᵀ + α * y * xᵀ + A` for the symmetric matrix `A` whose triangle
`uplo` is packed in `ap`, by the loops of the reference BLAS (`dspr2`): for each column `j`, it adds
`x` times `α * y[j]` and `y` times `α * x[j]` to each element of the column of the triangle, in that
order. As in the reference BLAS, it returns `ap` when `α = 0`, and skips the columns with
`x[j] = y[j] = 0`. It updates `ap` in place when its array is not shared, and leaves the elements of
the array outside `ap` unchanged.
-/
@[expose] public def spr2 (uplo : Uplo) (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    Vec (n * (n + 1) / 2) :=
  if α == 0 then ap
  else
    { data := spr2Data uplo α x y ap
      off := ap.off
      inc := ap.inc
      inc_pos := ap.inc_pos
      bound := by rw [spr2Data_eq, size_modifyAt]; exact ap.bound }

public theorem data_spr2 (uplo : Uplo) (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2)) :
    (spr2 uplo α x y ap).data = ap.data.modifyAt ap.stride.idx 0 (n * (n + 1) / 2) fun p v =>
      if α == 0 then v else spr2At uplo α x y p v := by
  unfold spr2
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, spr2Data_eq]
  · simp only [↓reduceIte]
    exact (modifyAt_id _ _ _ _).symm

@[simp] public theorem off_spr2 (uplo : Uplo) (α : Float32) (x y : Vec n)
    (ap : Vec (n * (n + 1) / 2)) : (spr2 uplo α x y ap).off = ap.off := by
  unfold spr2; split <;> rfl

@[simp] public theorem inc_spr2 (uplo : Uplo) (α : Float32) (x y : Vec n)
    (ap : Vec (n * (n + 1) / 2)) : (spr2 uplo α x y ap).inc = ap.inc := by
  unfold spr2; split <;> rfl

/-- Element `p` of `spr2 uplo α x y ap` is `ap[p]` when `α = 0`, and `spr2At` of it otherwise. -/
public theorem getElem_spr2 (uplo : Uplo) (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2))
    (p : Nat) (h : p < n * (n + 1) / 2) :
    (spr2 uplo α x y ap)[p] = if α == 0 then ap[p] else spr2At uplo α x y p ap[p] :=
  Vec.getElem_of_data_eq_modifyAt _ (data_spr2 uplo α x y ap) (off_spr2 uplo α x y ap)
    (inc_spr2 uplo α x y ap) p h

/-- Column `j` of the loops of `spr2` is the only one that updates the element `i` of column `j`. -/
private theorem spr2At_col (uplo : Uplo) (α : Float32) (x y : Vec n) {i j : Nat} (hj : j < n)
    (hi : packedRow uplo j ≤ i) (hi' : i < packedRow uplo j + packedLen uplo n j) (v : Float32) :
    spr2At uplo α x y (packedStart uplo n j + (i - packedRow uplo j)) v =
      if x.data[x.off + x.inc * j]! == 0 && y.data[y.off + y.inc * j]! == 0 then v
      else v + x.data[x.off + x.inc * i]! * (α * y.data[y.off + y.inc * j]!) +
        y.data[y.off + y.inc * i]! * (α * x.data[x.off + x.inc * j]!) := by
  rw [spr2At, fold_single hj (fun j' v => spr2Col uplo α x y j'
    (packedStart uplo n j + (i - packedRow uplo j)) v)]
  · unfold spr2Col
    cases x.data[x.off + x.inc * j]! == 0 && y.data[y.off + y.inc * j]! == 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
        show packedRow uplo j + (packedStart uplo n j + (i - packedRow uplo j) -
          packedStart uplo n j) = i by lia]
    · simp only [↓reduceIte]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
  · intro j' hj' hne v
    unfold spr2Col
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun ⟨h₁, h₂⟩ => hne
      (packedStart_unique hj hj' (Nat.le_add_right _ _) (by lia) h₁ (by split at h₂ <;> lia)))]

/--
Element `(i, j)` of the packed upper triangle of `spr2 .upper α x y ap`, for `i ≤ j`, is
`ap[upIdx j i]` when `α = 0` or `x[j] = y[j] = 0`, and
`ap[upIdx j i] + x[i] * (α * y[j]) + y[i] * (α * x[j])` otherwise.
-/
public theorem getElem_spr2_upper (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2))
    {i j : Nat} (hij : i ≤ j) (hj : j < n) :
    (spr2 .upper α x y ap)[upIdx j i]'(upIdx_lt hij hj) =
      if α == 0 || (x[j] == 0 && y[j] == 0) then ap[upIdx j i]'(upIdx_lt hij hj)
      else ap[upIdx j i]'(upIdx_lt hij hj) + x[i]'(by lia) * (α * y[j]) +
        y[i]'(by lia) * (α * x[j]) := by
  rw [getElem_spr2]
  have e : spr2At .upper α x y (upIdx j i) (ap[upIdx j i]'(upIdx_lt hij hj)) = _ :=
    spr2At_col .upper α x y hj (Nat.zero_le i) (show i < 0 + (j + 1) by lia) _
  rw [e, getElem!_pos x.data (x.off + x.inc * i) (x.index_lt (by lia)),
    getElem!_pos x.data (x.off + x.inc * j) (x.index_lt hj),
    getElem!_pos y.data (y.off + y.inc * i) (y.index_lt (by lia)),
    getElem!_pos y.data (y.off + y.inc * j) (y.index_lt hj)]
  cases α == 0 <;> cases x[j] == 0 <;> cases y[j] == 0 <;> rfl

/--
Element `(i, j)` of the packed lower triangle of `spr2 .lower α x y ap`, for `i ≥ j`, is
`ap[loIdx n j i]` when `α = 0` or `x[j] = y[j] = 0`, and
`ap[loIdx n j i] + x[i] * (α * y[j]) + y[i] * (α * x[j])` otherwise.
-/
public theorem getElem_spr2_lower (α : Float32) (x y : Vec n) (ap : Vec (n * (n + 1) / 2))
    {i j : Nat} (hji : j ≤ i) (hi : i < n) :
    (spr2 .lower α x y ap)[loIdx n j i]'(loIdx_lt hji hi) =
      if α == 0 || (x[j]'(by lia) == 0 && y[j]'(by lia) == 0) then
        ap[loIdx n j i]'(loIdx_lt hji hi)
      else ap[loIdx n j i]'(loIdx_lt hji hi) + x[i] * (α * y[j]'(by lia)) +
        y[i] * (α * x[j]'(by lia)) := by
  rw [getElem_spr2]
  have e : spr2At .lower α x y (loIdx n j i) (ap[loIdx n j i]'(loIdx_lt hji hi)) = _ :=
    spr2At_col .lower α x y (i := i) (j := j) (by lia) hji (show i < j + (n - j) by lia) _
  rw [e, getElem!_pos x.data (x.off + x.inc * i) (x.index_lt hi),
    getElem!_pos x.data (x.off + x.inc * j) (x.index_lt (by lia)),
    getElem!_pos y.data (y.off + y.inc * i) (y.index_lt hi),
    getElem!_pos y.data (y.off + y.inc * j) (y.index_lt (by lia))]
  cases α == 0 <;> cases x[j] == 0 <;> cases y[j] == 0 <;> rfl

end Mat

end BLAS.Float32
