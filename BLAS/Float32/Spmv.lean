/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Packed
public import BLAS.Float32.Trsv
import all BLAS.Internal

/-!
# Packed symmetric matrix-vector product

`Mat.spmv uplo α ap x β y` computes `α * A * x + β * y` for the symmetric matrix `A` whose triangle
`uplo` is packed in `ap` as for `Mat.tpmv`, by the loops of the reference BLAS (`dspmv`): it first
scales `y` by `β` (setting it to `0` when `β = 0`), and then, for each column `j` of the triangle,
adds `α * x[j]` times the column to the other elements of `y` in the triangle, and to `y[j]` the
diagonal term and `α` times the dot product of the column with `x`. Each element of `y` gets these
terms in the order of the loops, as for `Mat.symv` and `Mat.sbmv`.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {n : Nat}

/-! ## The loops -/

/-- A loop whose step `i` adds `g i` to its variable and maps its array by `F i`. -/
private theorem iterRange_pair (g : Nat → Float32) (F : Nat → Float32Array → Float32Array)
    (k : Nat) (s : Float32) (a : Float32Array) :
    iterRange (fun i p => (p.1 + g i, F i p.2)) 0 k (s, a) =
      (Nat.fold k (fun i _ s => s + g i) s, iterRange F 0 k a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, iterRange_succ _ (Nat.zero_le _),
      Nat.fold_succ]

/-- Steps that each write `G i c[idx i]!` at `idx i` are a `modifyAt`. -/
private theorem iterRange_set!_self (a : Float32Array) (idx : Nat → Nat)
    (G : Nat → Float32 → Float32) {lo hi : Nat} :
    iterRange (fun i c => c.set! (idx i) (G i c[idx i]!)) lo hi a = a.modifyAt idx lo hi G := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), modifyAt_of_lt _ _ (by lia), ih _ (by lia)]

/-! ## The upper triangle -/

/--
The dot product of column `j` of the packed upper triangle, above the diagonal, with `x`: the terms
`A[i, j] * x[i]` for `i = 0, …, j - 1`, from `0`.
-/
@[expose] public def spmvUpperDot (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) : Float32 :=
  Nat.fold j (fun l _ s =>
    s + ap.data[ap.off + ap.inc * upIdx j l]! * x.data[x.off + x.inc * l]!) 0

/--
The step `j` of the upper product: add `α * x[j]` times column `j` to the elements above `j`, and
the diagonal term and `α` times `spmvUpperDot ap x j` to element `j`.
-/
@[expose] public def spmvUpperStep (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x y : Vec n)
    (j : Nat) (c : Float32Array) : Float32Array :=
  c.modifyAt y.stride.idx 0 n fun i v =>
    if i = j then
      v + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * upIdx j j]! +
        α * spmvUpperDot ap x j
    else if i < j then v + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * upIdx j i]!
    else v

/-- The loops of the upper product on the array `c` of `y`, already scaled by `β`. -/
public def spmvUpperData (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x y : Vec n)
    (hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) : Float32Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  have hn := tri_lt_size ap hs.1
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let po := ap.off.toUSize
  let pc := ap.inc.toUSize
  (inplace c do
    for j in 0...nu do
      have hjn : j.toNat < n := by lia
      let t := α * x.uget xo xc rfl rfl hs.2.1 j hjn
      for l in 0...j with (s := 0) do
        have hp := toNat_packedUp_add hn hjn (l := l) (Nat.le_of_lt (by assumption))
        have hi : l.toNat < n := Nat.lt_trans (by assumption) hjn
        have hq : (o + cc * l).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let aij := ap.uget po pc rfl rfl hs.1 (packedUp j + l) (hp.1 ▸ hp.2)
        c[o + cc * l] := c[o + cc * l] + t * aij
        s := s + aij * x.uget xo xc rfl rfl hs.2.1 l hi
      have hq : (o + cc * j).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hjn
      have hd := toNat_packedUp_add hn hjn (l := j) (Nat.le_refl _)
      c[o + cc * j] :=
        c[o + cc * j] + t * ap.uget po pc rfl rfl hs.1 (packedUp j + j) (hd.1 ▸ hd.2) + α * s).2

public theorem spmvUpperData_eq_iterRange (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x y : Vec n)
    (hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) :
    spmvUpperData α ap x y hs o cc ho hcc c hc = iterRange (spmvUpperStep α ap x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  have hn := tri_lt_size ap hs.1
  subst ho hcc
  unfold spmvUpperData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := spmvUpperStep α ap x y)
    (hF := fun _ _ => by unfold spmvUpperStep; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hnu]
  · intro j _ hj next a h
    rw [hnu] at hj
    have hp : (y.off.toUSize + y.inc.toUSize * j).toNat = y.off + y.inc * j.toNat :=
      y.toNat_index hs.2.2 hj
    have hd := toNat_packedUp_add hn hj (l := j) (Nat.le_refl _)
    rw [Tail.run_forInFrom (f := fun l p =>
        (p.1 + ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + l)]! *
            x.data[x.off + x.inc * l]!,
          p.2.set! (y.off + y.inc * (0 + l))
            (p.2[y.off + y.inc * (0 + l)]! + α * x.data[x.off + x.inc * j.toNat]! *
              ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + l)]!)))
      (hf := by simp)]
    · have hpair := iterRange_pair
        (fun l => ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + l)]! *
          x.data[x.off + x.inc * l]!)
        (fun l c => c.set! (y.off + y.inc * (0 + l))
          (c[y.off + y.inc * (0 + l)]! + α * x.data[x.off + x.inc * j.toNat]! *
            ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + l)]!)) j.toNat 0 a
      rw [iterRange_set!_self a (fun l => y.off + y.inc * (0 + l))
        (fun l v => v + α * x.data[x.off + x.inc * j.toNat]! *
          ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + l)]!)] at hpair
      simp only [USize.toNat_zero, Tail.run_readThen, Tail.run_writeThen]
      apply run_congr
      simp only [hpair, Vec.uget_eq_getElem, Vec.getElem_def, hp, hd.1]
      rw [set_eq_set!]
      simp only [getElem_eq_getElem!]
      rw [set!_modifyAt_band y a (h.trans hc) 0 j.toNat j.toNat (by lia) hj (by lia) _
        (fun v => v + α * x.data[x.off + x.inc * j.toNat]! *
          ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + j.toNat)]! +
          α * Nat.fold j.toNat (fun i _ s =>
            s + ap.data[ap.off + ap.inc * (j.toNat * (j.toNat + 1) / 2 + i)]! *
              x.data[x.off + x.inc * i]!) 0), spmvUpperStep]
      apply modifyAt_congr_fun
      intro i v _ _
      by_cases h₁ : i = j.toNat
      · simp only [h₁, ↓reduceIte, spmvUpperDot, upIdx]
      · simp only [h₁, ↓reduceIte, upIdx, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
    · intro l _ hl next' s a' h'
      have hl' := toNat_packedUp_add hn hj (l := l) (by lia)
      have hq : (y.off.toUSize + y.inc.toUSize * l).toNat = y.off + y.inc * (0 + l.toNat) := by
        rw [y.toNat_index hs.2.2 (by lia), Nat.zero_add]
      simp only [Tail.run_readThen, Tail.run_writeThen, Vec.uget_eq_getElem, Vec.getElem_def, hq,
        hl'.1]
      simp only [getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _

/--
The value of element `i` of the upper product, from its value `v` after the scaling: `v` plus the
diagonal term and `α` times the dot product of column `i`, then the terms `α * x[j] * A[i, j]` for
`j = i + 1, …, n - 1`.
-/
@[expose] public def spmvUpperAt (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat)
    (v : Float32) : Float32 :=
  Nat.fold (n - 1 - i) (fun t _ s =>
      s + α * x.data[x.off + x.inc * (i + 1 + t)]! *
        ap.data[ap.off + ap.inc * upIdx (i + 1 + t) i]!)
    (v + α * x.data[x.off + x.inc * i]! * ap.data[ap.off + ap.inc * upIdx i i]! +
      α * spmvUpperDot ap x i)

/-- The loops of the upper product map the array of the scaled `y` by `spmvUpperAt`. -/
public theorem spmvUpperData_eq (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x y : Vec n)
    (hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) :
    spmvUpperData α ap x y hs o cc ho hcc c hc =
      c.modifyAt y.stride.idx 0 n (spmvUpperAt α ap x) := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  rw [spmvUpperData_eq_iterRange, show spmvUpperStep α ap x y = fun j c =>
      c.modifyAt y.stride.idx 0 n fun i v =>
        if i = j then
          v + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * upIdx j j]! +
            α * spmvUpperDot ap x j
        else if i < j then
          v + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * upIdx j i]!
        else v from rfl, iterRange_modifyAt _ _ hinj]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [fold_upper_tri hi (fun j s => s + α * x.data[x.off + x.inc * j]! *
      ap.data[ap.off + ap.inc * upIdx j j]! + α * spmvUpperDot ap x j)
    (fun j s => s + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * upIdx j i]!),
    spmvUpperAt]

/-! ## The lower triangle -/

/--
The dot product of column `j` of the packed lower triangle, below the diagonal, with `x`: the terms
`A[i, j] * x[i]` for `i = j + 1, …, n - 1`, from `0`.
-/
@[expose] public def spmvLowerDot (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) : Float32 :=
  Nat.fold (n - 1 - j) (fun l _ s =>
    s + ap.data[ap.off + ap.inc * loIdx n j (j + 1 + l)]! * x.data[x.off + x.inc * (j + 1 + l)]!) 0

/--
The step `j` of the lower product: add `α * x[j]` times column `j` to the elements below `j`, and
the diagonal term and `α` times `spmvLowerDot ap x j` to element `j`.
-/
@[expose] public def spmvLowerStep (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x y : Vec n)
    (j : Nat) (c : Float32Array) : Float32Array :=
  c.modifyAt y.stride.idx 0 n fun i v =>
    if i = j then
      v + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * loIdx n j j]! +
        α * spmvLowerDot ap x j
    else if j < i then
      v + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * loIdx n j i]!
    else v

/-- The loops of the lower product on the array `c` of `y`, already scaled by `β`. -/
public def spmvLowerData (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x y : Vec n)
    (hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) : Float32Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  have hn := tri_lt_size ap hs.1
  have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let po := ap.off.toUSize
  let pc := ap.inc.toUSize
  (inplace c do
    for j in 0...nu do
      have hjn : j.toNat < n := by lia
      let t := α * x.uget xo xc rfl rfl hs.2.1 j hjn
      have hq : (o + cc * j).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hjn
      have hd := toNat_packedLo hn hjn
      let d := c[o + cc * j] + t * ap.uget po pc rfl rfl hs.1 (packedLo n j) (hd.1 ▸ hd.2)
      for l in 0...bandBelow n n j with (s := 0) do
        have hl := toNat_bandBelow_add hn' hjn (by assumption)
        have hp := toNat_packedLo_below hn hn' hjn (by assumption)
        have hi : (j + 1 + l).toNat < n := hl.1 ▸ hl.2
        have hq' : (o + cc * (j + 1 + l)).toNat < c.size :=
          hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let aij := ap.uget po pc rfl rfl hs.1 (packedLo n j + (1 + l)) (hp.1 ▸ hp.2)
        c[o + cc * (j + 1 + l)] := c[o + cc * (j + 1 + l)] + t * aij
        s := s + aij * x.uget xo xc rfl rfl hs.2.1 (j + 1 + l) hi
      c[o + cc * j] := d + α * s).2

public theorem spmvLowerData_eq_iterRange (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x y : Vec n)
    (hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) :
    spmvLowerData α ap x y hs o cc ho hcc c hc = iterRange (spmvLowerStep α ap x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  have hn := tri_lt_size ap hs.1
  have hn' : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
  subst ho hcc
  unfold spmvLowerData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := spmvLowerStep α ap x y)
    (hF := fun _ _ => by unfold spmvLowerStep; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hnu]
  · intro j _ hj next a h
    rw [hnu] at hj
    have hp : (y.off.toUSize + y.inc.toUSize * j).toNat = y.off + y.inc * j.toNat :=
      y.toNat_index hs.2.2 hj
    have hd := toNat_packedLo hn hj
    have hbe : (bandBelow n n j).toNat = n - 1 - j.toNat := by
      rw [toNat_bandBelow hn']; lia
    simp only [Tail.run_readThen]
    rw [Tail.run_forInFrom (f := fun l p =>
        (p.1 + ap.data[ap.off + ap.inc *
              (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + (1 + l))]! *
            x.data[x.off + x.inc * (j.toNat + 1 + l)]!,
          p.2.set! (y.off + y.inc * (j.toNat + 1 + l)) (p.2[y.off + y.inc * (j.toNat + 1 + l)]! +
            α * x.data[x.off + x.inc * j.toNat]! * ap.data[ap.off + ap.inc *
              (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + (1 + l))]!)))
      (hf := by simp)]
    · have hpair := iterRange_pair
        (fun l => ap.data[ap.off + ap.inc *
            (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + (1 + l))]! *
          x.data[x.off + x.inc * (j.toNat + 1 + l)]!)
        (fun l c => c.set! (y.off + y.inc * (j.toNat + 1 + l))
          (c[y.off + y.inc * (j.toNat + 1 + l)]! + α * x.data[x.off + x.inc * j.toNat]! *
            ap.data[ap.off + ap.inc *
              (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + (1 + l))]!))
        (n - 1 - j.toNat) 0 a
      rw [iterRange_set!_self a (fun l => y.off + y.inc * (j.toNat + 1 + l)) (fun l v =>
        v + α * x.data[x.off + x.inc * j.toNat]! * ap.data[ap.off + ap.inc *
          (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + (1 + l))]!)] at hpair
      simp only [USize.toNat_zero, Tail.run_writeThen, hbe]
      apply run_congr
      simp only [hpair, Vec.uget_eq_getElem, Vec.getElem_def, hp, hd.1]
      rw [set_eq_set!]
      simp only [getElem_eq_getElem!]
      have hne := getElem!_modifyAt_of_ne a (fun l => y.off + y.inc * (j.toNat + 1 + l))
        (lo := 0) (hi := n - 1 - j.toNat) (fun l v =>
          v + α * x.data[x.off + x.inc * j.toNat]! * ap.data[ap.off + ap.inc *
            (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + (1 + l))]!)
        (p := y.off + y.inc * j.toNat) (fun l _ hl e => by
          have := y.fits.injOn (lo := 0) (Nat.le_refl _) (j.toNat + 1 + l) (Nat.zero_le _)
            (by lia) j.toNat (Nat.zero_le _) hj e
          lia)
      rw [← hne]
      rw [set!_modifyAt_band y a (h.trans hc) (j.toNat + 1) (n - 1 - j.toNat) j.toNat
        (by lia) hj (by lia) (w := fun v =>
          v + α * x.data[x.off + x.inc * j.toNat]! *
            ap.data[ap.off + ap.inc * (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2)]! +
            α * Nat.fold (n - 1 - j.toNat) (fun i _ s =>
              s + ap.data[ap.off + ap.inc *
                  (n * (n + 1) / 2 - (n - j.toNat) * (n - j.toNat + 1) / 2 + (1 + i))]! *
                x.data[x.off + x.inc * (j.toNat + 1 + i)]!) 0), spmvLowerStep]
      apply modifyAt_congr_fun
      intro i v _ _
      have e : ∀ l, j.toNat + 1 + l - j.toNat = 1 + l := fun l => by lia
      by_cases h₁ : i = j.toNat
      · simp only [h₁, ↓reduceIte, spmvLowerDot, loIdx, Nat.sub_self, Nat.add_zero, e]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁),
          ite_eq_right_of_eq_false _ _ (eq_false h₁)]
        by_cases h₂ : j.toNat < i
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
            ite_eq_left_of_eq_true _ _ (eq_true h₂), loIdx,
            show 1 + (i - (j.toNat + 1)) = i - j.toNat by lia]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia)),
            ite_eq_right_of_eq_false _ _ (eq_false h₂)]
    · intro l _ hl next' s a' h'
      have hl' := toNat_bandBelow_add (k := n) hn' hj (l := l) hl
      have hr := toNat_one_add_bandBelow (k := n) hn' (j := j) (l := l) hl
      have hpl := toNat_packedLo_below hn hn' hj hl
      have hq : (y.off.toUSize + y.inc.toUSize * (j + 1 + l)).toNat =
          y.off + y.inc * (j.toNat + 1 + l.toNat) := by
        rw [y.toNat_index hs.2.2 (by rw [hl'.1]; exact hl'.2), hl'.1]
      simp only [Tail.run_readThen, Tail.run_writeThen, Vec.uget_eq_getElem, Vec.getElem_def, hq,
        hl'.1, hpl.1, hr.1]
      simp only [getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _

/--
The value of element `i` of the lower product, from its value `v` after the scaling: `v` plus the
terms `α * x[j] * A[i, j]` for `j = 0, …, i - 1`, then the diagonal term and `α` times the dot
product of column `i`.
-/
@[expose] public def spmvLowerAt (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (i : Nat)
    (v : Float32) : Float32 :=
  Nat.fold i (fun t _ s =>
      s + α * x.data[x.off + x.inc * t]! * ap.data[ap.off + ap.inc * loIdx n t i]!) v +
    α * x.data[x.off + x.inc * i]! * ap.data[ap.off + ap.inc * loIdx n i i]! +
      α * spmvLowerDot ap x i

/-- The loops of the lower product map the array of the scaled `y` by `spmvLowerAt`. -/
public theorem spmvLowerData_eq (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x y : Vec n)
    (hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) :
    spmvLowerData α ap x y hs o cc ho hcc c hc =
      c.modifyAt y.stride.idx 0 n (spmvLowerAt α ap x) := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  rw [spmvLowerData_eq_iterRange, show spmvLowerStep α ap x y = fun j c =>
      c.modifyAt y.stride.idx 0 n fun i v =>
        if i = j then
          v + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * loIdx n j j]! +
            α * spmvLowerDot ap x j
        else if j < i then
          v + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * loIdx n j i]!
        else v from rfl, iterRange_modifyAt _ _ hinj]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [fold_lower_tri hi (fun j s => s + α * x.data[x.off + x.inc * j]! *
      ap.data[ap.off + ap.inc * loIdx n j j]! + α * spmvLowerDot ap x j)
    (fun j s => s + α * x.data[x.off + x.inc * j]! * ap.data[ap.off + ap.inc * loIdx n j i]!),
    spmvLowerAt]

/-! ## `spmv` -/

/-- The value of element `i` of the product on the triangle `uplo`, from its scaled value `v`. -/
@[expose] public def spmvAt (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Nat → Float32 → Float32 :=
  match uplo with
  | .upper => spmvUpperAt α ap x
  | .lower => spmvLowerAt α ap x

/--
The value of `spmv` at the index `i` of `y`, from its old value `v`: `betaMul β v` when `α = 0`,
and otherwise `spmvAt` of it.
-/
@[expose] public def spmvVal (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float32) (i : Nat) (v : Float32) : Float32 :=
  if α == 0 then betaMul β v else spmvAt uplo α ap x i (betaMul β v)

/-- The array of `spmv`. -/
public def spmvData (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float32) (y : Vec n) : Float32Array :=
  if hs : ap.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let o := y.off.toUSize
    let cc := y.inc.toUSize
    if α == 0 then y.scalBetaData β
    else match uplo with
      | .upper => spmvUpperData α ap x y hs o cc rfl rfl (y.scalBetaData β)
          (by rw [Vec.scalBetaData_eq, size_modifyAt])
      | .lower => spmvLowerData α ap x y hs o cc rfl rfl (y.scalBetaData β)
          (by rw [Vec.scalBetaData_eq, size_modifyAt])
  else y.data.modifyAt y.stride.idx 0 n (spmvVal uplo α ap x β)

public theorem spmvData_eq (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float32) (y : Vec n) :
    spmvData uplo α ap x β y = y.data.modifyAt y.stride.idx 0 n (spmvVal uplo α ap x β) := by
  have hinj := y.fits.injOn (lo := 0) (Nat.le_refl _)
  unfold spmvData
  split
  · rename_i hs
    cases hα : α == 0
    · cases uplo
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [spmvUpperData_eq, Vec.scalBetaData_eq, modifyAt_modifyAt _ _ hinj]
        apply modifyAt_congr_fun
        intro i v _ _
        simp [spmvVal, spmvAt, hα]
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [spmvLowerData_eq, Vec.scalBetaData_eq, modifyAt_modifyAt _ _ hinj]
        apply modifyAt_congr_fun
        intro i v _ _
        simp [spmvVal, spmvAt, hα]
    · simp only [↓reduceIte]
      rw [Vec.scalBetaData_eq]
      apply modifyAt_congr_fun
      intro i v _ _
      simp [spmvVal, hα]
  · rfl

/--
`spmv uplo α ap x β y` is `α * A * x + β * y` for the symmetric matrix `A` whose triangle `uplo` is
packed in `ap`, over `y`, by the loops of the reference BLAS (`dspmv`). It updates `y` in place when
its array is not shared, and leaves the elements of the array outside `y` unchanged. As in the
reference BLAS, it sets `y` to `0` before adding the terms when `β = 0`, and only scales `y` when
`α = 0`.
-/
@[expose] public def spmv (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float32) (y : Vec n) : Vec n where
  data := spmvData uplo α ap x β y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [spmvData_eq, size_modifyAt]; exact y.bound

/-- The array of `spmv uplo α ap x β y` is the array of `y` with its elements updated. -/
public theorem data_spmv (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float32) (y : Vec n) :
    (spmv uplo α ap x β y).data = y.data.modifyAt y.stride.idx 0 n (spmvVal uplo α ap x β) :=
  spmvData_eq uplo α ap x β y

@[simp] public theorem off_spmv (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) (β : Float32) (y : Vec n) : (spmv uplo α ap x β y).off = y.off := rfl

@[simp] public theorem inc_spmv (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) (β : Float32) (y : Vec n) : (spmv uplo α ap x β y).inc = y.inc := rfl

/-- Element `i` of `spmv uplo α ap x β y` is `spmvVal` of `y[i]`. -/
public theorem getElem_spmv (uplo : Uplo) (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float32) (y : Vec n) (i : Nat) (h : i < n) :
    (spmv uplo α ap x β y)[i] = spmvVal uplo α ap x β i y[i] :=
  Vec.getElem_of_data_eq_modifyAt _ (data_spmv uplo α ap x β y) (off_spmv uplo α ap x β y)
    (inc_spmv uplo α ap x β y) i h

/--
Element `i` of `spmv .upper α ap x β y` is `betaMul β y[i]` when `α = 0`, and otherwise
`betaMul β y[i] + α * x[i] * A[i, i] + α * t`, with `t` the sum of the terms `A[l, i] * x[l]` for
`l < i`, plus the terms `α * x[i + 1 + t] * A[i, i + 1 + t]` for `t < n - 1 - i`, where `A[i, j]`
is `ap[upIdx j i]` for `i ≤ j`.
-/
public theorem getElem_spmv_upper (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float32) (y : Vec n) (i : Nat) (h : i < n) :
    (spmv .upper α ap x β y)[i] =
      if α == 0 then betaMul β y[i]
      else Nat.fold (n - 1 - i) (fun t _ s =>
          s + α * x[i + 1 + t]'(by lia) * ap[upIdx (i + 1 + t) i]'(upIdx_lt (by lia) (by lia)))
        (betaMul β y[i] + α * x[i] * ap[upIdx i i]'(upIdx_lt (Nat.le_refl i) h) +
          α * Nat.fold i (fun l _ s =>
            s + ap[upIdx i l]'(upIdx_lt (by lia) h) * x[l]'(by lia)) 0) := by
  rw [getElem_spmv _ _ _ _ _ _ _ h, spmvVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, spmvAt, spmvUpperAt, spmvUpperDot]
    rw [getElem!_pos x.data _ (x.index_lt h),
      getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (Nat.le_refl i) h))]
    congr 1
    · funext t ht s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (by lia) (by lia)))]
      rfl
    · congr 3
      funext l hl s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos ap.data _ (ap.index_lt (upIdx_lt (by lia) h))]
      rfl
  · simp only [↓reduceIte]

/--
Element `i` of `spmv .lower α ap x β y` is `betaMul β y[i]` when `α = 0`, and otherwise
`betaMul β y[i]` plus the terms `α * x[j] * A[i, j]` for `j = 0, …, i - 1`, plus
`α * x[i] * A[i, i] + α * t`, with `t` the sum of the terms `A[i + 1 + l, i] * x[i + 1 + l]` for
`l < n - 1 - i`, where `A[i, j]` is `ap[loIdx n j i]` for `i ≥ j`.
-/
public theorem getElem_spmv_lower (α : Float32) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float32) (y : Vec n) (i : Nat) (h : i < n) :
    (spmv .lower α ap x β y)[i] =
      if α == 0 then betaMul β y[i]
      else Nat.fold i (fun t _ s =>
          s + α * x[t]'(by lia) * ap[loIdx n t i]'(loIdx_lt (by lia) h)) (betaMul β y[i]) +
        α * x[i] * ap[loIdx n i i]'(loIdx_lt (Nat.le_refl i) h) +
        α * Nat.fold (n - 1 - i) (fun l _ s =>
          s + ap[loIdx n i (i + 1 + l)]'(loIdx_lt (by lia) (by lia)) *
            x[i + 1 + l]'(by lia)) 0 := by
  rw [getElem_spmv _ _ _ _ _ _ _ h, spmvVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, spmvAt, spmvLowerAt, spmvLowerDot]
    rw [getElem!_pos x.data _ (x.index_lt h),
      getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (Nat.le_refl i) h))]
    congr 2
    · congr 1
      · congr 1
        funext t ht s
        rw [getElem!_pos x.data _ (x.index_lt (by lia)),
          getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (by lia) h))]
        rfl
    · congr 2
      funext l hl s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos ap.data _ (ap.index_lt (loIdx_lt (by lia) (by lia)))]
      rfl
  · simp only [↓reduceIte]

end Mat

end BLAS.Float32
