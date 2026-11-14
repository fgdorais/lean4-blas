/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Trsv
public import BLAS.Float32.Level2
import all BLAS.Internal

/-!
# Symmetric rank-k update

`Mat.syrk uplo α A β C` is `α * A * Aᵀ + β * C` and `Mat.syrkT uplo α A β C` is
`α * Aᵀ * A + β * C`, on the triangle `uplo` of `C`, by the loops of the reference BLAS. Each
element gets the operations of those loops, in the same order, with the special cases of the
reference BLAS: `syrk` skips the terms with `A[j, l] = 0`, both only scale `C` when `α = 0`, and
`syrkT` leaves `C` unchanged when `k = 0` and `β = 1`.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

/-- Whether the element `(i, j)` is in the triangle `u`: `i ≤ j` for `.upper`, `j ≤ i` for `.lower`. -/
@[expose] public def Uplo.contains : Uplo → Nat → Nat → Bool
  | .upper, i, j => decide (i ≤ j)
  | .lower, i, j => decide (j ≤ i)

/-- The first row of column `j` in the triangle `u`. -/
@[expose] public def Uplo.lo : Uplo → Nat → Nat
  | .upper, _ => 0
  | .lower, j => j

/-- The row after the last of column `j` in the triangle `u` of an `n × n` matrix. -/
@[expose] public def Uplo.hi : Uplo → Nat → Nat → Nat
  | .upper, _, j => j + 1
  | .lower, n, _ => n

/-- Row `i < n` of column `j < n` is in the triangle when it is between `lo` and `hi`. -/
public theorem Uplo.contains_iff (u : Uplo) {n i j : Nat} (hin : i < n) :
    u.contains i j = true ↔ u.lo j ≤ i ∧ i < u.hi n j := by
  cases u <;> grind [Uplo.contains, Uplo.lo, Uplo.hi]

public theorem Uplo.hi_le (u : Uplo) {n j : Nat} (hj : j < n) : u.hi n j ≤ n := by
  cases u <;> grind [Uplo.hi]

public theorem Uplo.lo_le_hi (u : Uplo) {n j : Nat} (hj : j < n) : u.lo j ≤ u.hi n j := by
  cases u <;> grind [Uplo.lo, Uplo.hi]

/--
`Uplo.lo` on `USize`. It is not inlined, so that the column loop has a single copy of each inner
loop, which the C compiler inlines and vectorizes.
-/
@[noinline, expose] public def Uplo.loU : Uplo → USize → USize
  | .upper, _ => 0
  | .lower, j => j

/-- `Uplo.hi` on `USize`, not inlined, as `Uplo.loU`. -/
@[noinline, expose] public def Uplo.hiU : Uplo → USize → USize → USize
  | .upper, _, j => j + 1
  | .lower, nu, _ => nu

public theorem Uplo.toNat_loU (u : Uplo) (j : USize) : (u.loU j).toNat = u.lo j.toNat := by
  cases u <;> simp [Uplo.loU, Uplo.lo]

public theorem Uplo.toNat_hiU (u : Uplo) {nu j : USize} {n : Nat} (hnu : nu.toNat = n)
    (hj : j.toNat < n) : (u.hiU nu j).toNat = u.hi n j.toNat := by
  cases u <;> grind [Uplo.hiU, Uplo.hi]

public theorem Uplo.loU_le_hiU (u : Uplo) {nu j : USize} {n : Nat} (hnu : nu.toNat = n)
    (hj : j.toNat < n) : (u.loU j).toNat ≤ (u.hiU nu j).toNat := by
  rw [u.toNat_loU, u.toNat_hiU hnu hj]; exact u.lo_le_hi hj

namespace Mat

variable {n k : Nat}

/-- The bound that a loop from `u.loU j` to `u.hiU nu j` gives its index. -/
private theorem lt_of_hiU {u : Uplo} {nu j i : USize} (hnu : nu.toNat = n) (hj : j.toNat < n)
    (hi : i.toNat < (u.hiU nu j).toNat) : i.toNat < n := by
  rw [u.toNat_hiU hnu hj] at hi
  exact Nat.lt_of_lt_of_le hi (u.hi_le hj)

/-! ## `syrk` -/

/--
The term `l` of the loops of `syrk` at `(i, j)`, added to `s`, on the arrays: `s` when `α = 0` or
`A[j, l] = 0`, which the reference BLAS skips, and `s + α * A[j, l] * A[i, l]` otherwise.
-/
@[expose] public def syrkTerm (α : Float32) (A : Mat n k) (l i j : Nat) (s : Float32) : Float32 :=
  if α == 0 || A.data[A.off + A.ld * l + j]! == 0 then s
  else s + α * A.data[A.off + A.ld * l + j]! * A.data[A.off + A.ld * l + i]!

/--
The value of the loops of `syrk` at `(i, j)` of the triangle, from its old value `v`, on the arrays:
`betaMul β v`, plus the terms `syrkTerm α A l i j` for `l = 0, …, k - 1`, from the left.
-/
@[expose] public def syrkSumAt (α : Float32) (A : Mat n k) (β : Float32) (i j : Nat) (v : Float32) :
    Float32 :=
  Nat.fold k (fun l _ s => syrkTerm α A l i j s) (betaMul β v)

/-- `syrkSumAt` in the triangle `uplo`, and the old value elsewhere. -/
@[expose] public def syrkAt (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (i j : Nat)
    (v : Float32) : Float32 :=
  if uplo.contains i j then syrkSumAt α A β i j v else v

/--
The row after the last that the loop of `syrk` updates for the term `l` of a column: `lo`, so that
the loop is empty, when the term is skipped. It is not inlined, as `Uplo.loU`.
-/
@[noinline, expose] public def syrkRows (lo hi : USize) (skip : Bool) : USize :=
  if skip then lo else hi

public theorem syrkRows_le {lo hi : USize} (h : lo.toNat ≤ hi.toNat) (skip : Bool) :
    (syrkRows lo hi skip).toNat ≤ hi.toNat := by
  unfold syrkRows; split <;> simp [h]

/--
The array of `C` with column `j` of `syrk` done: the triangle's part of the column scaled by `β`,
then the terms of `α * A[j, l]` times column `l` of `A` added to it, for `l = 0, …, k - 1`. The
columns run in a separate function, not in a third nested loop, so that the C compiler turns the
loops into jumps instead of calls, which would use stack for each term.
-/
public def syrkColData (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n)
    (j : Nat) (hj : j < n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ C.data.size < USize.size ∧ n < USize.size ∧
      k < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let ku := k.toUSize
    have hku : ku.toNat = k := by grind
    let ju := j.toUSize
    have hju : ju.toNat = j := by grind
    let c := C.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let cj := C.off.toUSize + C.ld.toUSize * ju
    let lo := uplo.loU ju
    let hi := uplo.hiU nu ju
    (inplace c do
      for i in lo...hi do
        have hk : (cj + 1 * i).toNat < c.size :=
          C.toNat_col_index_lt hs.2.1 (lt_of_hiU (u := uplo) (j := ju) hnu (by lia) (by assumption)) (by lia)
        c[cj + 1 * i] := betaMul β c[cj + 1 * i]
      for l in 0...ku do
        let ajl := A.uget ao al rfl rfl hs.1 ju l (by lia) (by lia)
        let t := α * ajl
        -- A skipped term runs an empty loop: an `if` would allocate a closure per term.
        let hi' := syrkRows lo hi (α == 0 || ajl == 0)
        have hh : hi'.toNat ≤ hi.toNat := syrkRows_le (uplo.loU_le_hiU hnu (by lia)) _
        for i in lo...hi' do
          have hk : (cj + 1 * i).toNat < c.size :=
            C.toNat_col_index_lt hs.2.1 (lt_of_hiU (u := uplo) (j := ju) hnu (by lia) (by lia)) (by lia)
          c[cj + 1 * i] := c[cj + 1 * i] +
            t * A.uget ao al rfl rfl hs.1 i l (lt_of_hiU (u := uplo) (j := ju) hnu (by lia) (by lia)) (by lia)).2
  else C.data.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v => syrkAt uplo α A β i j v

public theorem syrkColData_eq (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n)
    (j : Nat) (hj : j < n) :
    syrkColData uplo α A β C j hj =
      C.data.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v => syrkAt uplo α A β i j v := by
  unfold syrkColData
  split
  · rename_i hs
    have hnu : n.toUSize.toNat = n := by grind
    have hku : k.toUSize.toNat = k := by grind
    have hju : j.toUSize.toNat = j := by grind
    have hj' : j.toUSize.toNat < n := by lia
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v)
      (idx := (Stride.mk (C.off + C.ld * j.toUSize.toNat) 1).idx)
      (he := fun i _ hi => C.toNat_col_index hs.2.1 (lt_of_hiU (u := uplo) hnu hj' hi) hj')]
    · rw [Tail.run_forInFrom_unit (F := fun l c =>
        c.modifyAt (Stride.mk (C.off + C.ld * j.toUSize.toNat) 1).idx (uplo.lo j.toUSize.toNat)
          (uplo.hi n j.toUSize.toNat) fun i v => syrkTerm α A l i j.toUSize.toNat v) (hF := by simp)]
      · simp only [Tail.run_done, USize.toNat_zero, hku, uplo.toNat_loU, uplo.toNat_hiU hnu hj', hju]
        rw [iterRange_modifyAt _ _ (col_injOn _ _ _), modifyAt_modifyAt _ _ (col_injOn _ _ _),
          modifyAt_widen (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (uplo.lo_le_hi hj)
            (uplo.hi_le hj)]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [syrkAt, syrkSumAt]
        by_cases hc : uplo.contains i j = true
        · rw [ite_eq_left ((uplo.contains_iff hi).1 hc), ite_eq_left hc]
        · rw [ite_eq_right (fun h' => hc ((uplo.contains_iff hi).2 h')), ite_eq_right hc]
      · intro l _ hl next' a' h'
        rw [hku] at hl
        have hjl := getElem!_pos A.data (A.off + A.ld * l.toNat + j.toUSize.toNat)
          (A.index_lt hj' hl)
        rw [Tail.run_forInFrom_modify
          (G := fun i v => v + α * A.data[A.off + A.ld * l.toNat + j.toUSize.toNat]! *
            A.data[A.off + A.ld * l.toNat + i]!)
          (idx := (Stride.mk (C.off + C.ld * j.toUSize.toNat) 1).idx)
          (he := fun i _ hi => C.toNat_col_index hs.2.1 (lt_of_hiU (u := uplo) hnu hj'
            (Nat.lt_of_lt_of_le hi (syrkRows_le (uplo.loU_le_hiU hnu hj') _))) hj')]
        · apply run_congr
          simp only [syrkRows, uplo.toNat_loU, Mat.uget_eq_getElem, Mat.getElem_def, ← hjl]
          split
          next h0 =>
            rw [uplo.toNat_loU, modifyAt_of_le _ _ (Nat.le_refl _),
              modifyAt_congr_fun _ _ (g' := fun _ v => v)
                (fun i v _ _ => by rw [hju] at h0; simp [syrkTerm, hju, h0]), modifyAt_id]
          next h0 =>
            rw [uplo.toNat_hiU hnu hj']
            apply modifyAt_congr_fun
            intro i v _ _
            rw [hju] at h0
            simp [syrkTerm, hju, h0]
        · intro i _ hi v
          have hi' : i.toNat < n := lt_of_hiU (u := uplo) hnu hj'
            (Nat.lt_of_lt_of_le hi (syrkRows_le (uplo.loU_le_hiU hnu hj') _))
          simp only [Mat.uget_eq_getElem, Mat.getElem_def, ← hjl,
            getElem!_pos A.data (A.off + A.ld * l.toNat + i.toNat) (A.index_lt hi' hl)]
    · intro _ _ _ _; rfl
  · rfl


/-- The rows of the columns `j` and `j + 1 < n` of the triangle `u` are in order. -/
private theorem uplo_order2 (u : Uplo) {j : Nat} (hj : j + 1 < n) :
    u.lo j ≤ u.lo (j + 1) ∧ u.lo (j + 1) ≤ u.hi n j ∧ u.hi n j ≤ u.hi n (j + 1) ∧
      u.hi n (j + 1) ≤ n := by
  cases u <;> simp only [Uplo.lo, Uplo.hi] <;> lia

/--
Step `l` of `syrk` on the columns `j` and `j + 1` of a matrix at `off` with the leading dimension
`ld` in the array `a`: the rows of both columns that both terms update, a row of the two at a time,
then the other rows of each column. A skipped term updates no row of its column.
-/
@[expose] public def syrk2Step (uplo : Uplo) (α : Float32) (A : Mat n k) (off ld j l : Nat)
    (a : Float32Array) : Float32Array :=
  let a₀ := A.data[A.off + A.ld * l + j]!
  let a₁ := A.data[A.off + A.ld * l + (j + 1)]!
  let s₀ := α == 0 || a₀ == 0
  let s₁ := α == 0 || a₁ == 0
  let f₀ := fun i v => v + α * a₀ * A.data[A.off + A.ld * l + i]!
  let f₁ := fun i v => v + α * a₁ * A.data[A.off + A.ld * l + i]!
  let b₁ := if s₀ then uplo.lo (j + 1) else uplo.hi n j
  (((iterRange (fun i t => (t.set! (off + ld * j + i) (f₀ i t[off + ld * j + i]!)).set!
      (off + ld * (j + 1) + i) (f₁ i t[off + ld * (j + 1) + i]!)) (uplo.lo (j + 1))
      (if s₀ || s₁ then uplo.lo (j + 1) else uplo.hi n j) a).modifyAt
    (Stride.mk (off + ld * j) 1).idx (uplo.lo j)
      (if s₀ then uplo.lo j else if s₁ then uplo.hi n j else uplo.lo (j + 1)) f₀).modifyAt
    (Stride.mk (off + ld * (j + 1)) 1).idx b₁ (if s₁ then b₁ else uplo.hi n (j + 1)) f₁)

/-- `syrk2Step` adds the term `l` to the triangle's part of the columns `j` and `j + 1`. -/
theorem syrk2Step_mapMat (uplo : Uplo) (α : Float32) (A : Mat n k) (s : Float32Array)
    (off ld : Nat) (hml : n ≤ ld) {j : Nat} (hj : j + 1 < n)
    (hq : off + ld * (j + 1) + n ≤ s.size) (l : Nat) (H : Nat → Nat → Float32 → Float32) :
    syrk2Step uplo α A off ld j l (mapMat s off ld n j (j + 2) H) =
      mapMat s off ld n j (j + 2) fun i c v =>
        if uplo.contains i c then syrkTerm α A l i c (H i c v) else H i c v := by
  have hq₀ : off + ld * j + n ≤ s.size := by
    have := Nat.mul_le_mul_left ld (Nat.le_succ j); lia
  obtain ⟨o₁, o₂, o₃, o₄⟩ := uplo_order2 uplo hj
  have hR := iterRange_rows2_mapMat s off ld hml (lo := j) (hi := j + 2) ⟨Nat.le_refl j, by lia⟩
    ⟨by lia, by lia⟩ (by lia) hq₀ hq (r₀ := uplo.lo (j + 1))
    (r₁ := if (α == 0 || A.data[A.off + A.ld * l + j]! == 0) ||
      (α == 0 || A.data[A.off + A.ld * l + (j + 1)]! == 0) then uplo.lo (j + 1) else uplo.hi n j)
    (by split <;> lia) H
    (fun i v => v + α * A.data[A.off + A.ld * l + j]! * A.data[A.off + A.ld * l + i]!)
    (fun i v => v + α * A.data[A.off + A.ld * l + (j + 1)]! * A.data[A.off + A.ld * l + i]!)
  unfold syrk2Step
  dsimp only
  rw [hR,
    modifyAt_col_mapMat_mid s off ld hml ⟨Nat.le_refl j, by lia⟩ (by split <;> (try split) <;> lia),
    modifyAt_col_mapMat_mid s off ld hml ⟨by lia, by lia⟩ (by split <;> (try split) <;> lia)]
  apply mapMat_congr
  intro i c v hi h₁ h₂
  have hc : c = j ∨ c = j + 1 := by lia
  have e : ∀ c', uplo.contains i c' = true ↔ uplo.lo c' ≤ i ∧ i < uplo.hi n c' :=
    fun c' => uplo.contains_iff hi
  by_cases hs₀ : (α == 0 || A.data[A.off + A.ld * l + j]! == 0) = true <;>
  by_cases hs₁ : (α == 0 || A.data[A.off + A.ld * l + (j + 1)]! == 0) = true <;>
  rcases hc with rfl | rfl <;>
  simp only [syrkTerm, e, hs₀, hs₁, Bool.or_true, Bool.or_false, ite_true, ite_false,
    Bool.false_eq_true]
  all_goals (repeat' split)
  all_goals (first | rfl | (exfalso; lia))

/-- The steps `l < t` of `syrk2Step` add the terms `l < t` to the two columns. -/
theorem iterRange_syrk2Step (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (s : Float32Array)
    (off ld : Nat) (hml : n ≤ ld) {j : Nat} (hj : j + 1 < n)
    (hq : off + ld * (j + 1) + n ≤ s.size) (t : Nat) :
    iterRange (syrk2Step uplo α A off ld j) 0 t
        (mapMat s off ld n j (j + 2) fun i c v => if uplo.contains i c then betaMul β v else v) =
      mapMat s off ld n j (j + 2) fun i c v =>
        if uplo.contains i c then Nat.fold t (fun l _ x => syrkTerm α A l i c x) (betaMul β v)
        else v := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih, syrk2Step_mapMat uplo α A s off ld hml hj hq]
    apply mapMat_congr
    intro i c v _ _ _
    split <;> simp [Nat.fold_succ, *]

/-- The end of the rows of column `j` that the separate loop of `syrkCol2Data` updates. -/
@[noinline, expose] public def syrkRest0 (lo0 lo1 hi0 : USize) (s0 s1 : Bool) : USize :=
  if s0 then lo0 else if s1 then hi0 else lo1

/-- The start of the rows of column `j + 1` that the separate loop of `syrkCol2Data` updates. -/
@[noinline, expose] public def syrkRest1 (lo1 hi0 : USize) (s0 : Bool) : USize :=
  if s0 then lo1 else hi0

private theorem toNat_syrkRows (lo hi : USize) (skip : Bool) :
    (syrkRows lo hi skip).toNat = if skip then lo.toNat else hi.toNat := by
  unfold syrkRows; split <;> rfl

private theorem toNat_syrkRest0 (lo0 lo1 hi0 : USize) (s0 s1 : Bool) :
    (syrkRest0 lo0 lo1 hi0 s0 s1).toNat =
      if s0 then lo0.toNat else if s1 then hi0.toNat else lo1.toNat := by
  unfold syrkRest0; split <;> (try split) <;> rfl

private theorem toNat_syrkRest1 (lo1 hi0 : USize) (s0 : Bool) :
    (syrkRest1 lo1 hi0 s0).toNat = if s0 then lo1.toNat else hi0.toNat := by
  unfold syrkRest1; split <;> rfl

private theorem syrkRest0_le {lo0 lo1 hi0 : USize} (h₀ : lo0.toNat ≤ hi0.toNat)
    (h₁ : lo1.toNat ≤ hi0.toNat) (s0 s1 : Bool) : (syrkRest0 lo0 lo1 hi0 s0 s1).toNat ≤ hi0.toNat := by
  rw [toNat_syrkRest0]; split <;> (try split) <;> lia

private theorem syrkRest1_le {lo1 hi0 hi1 : USize} (h₀ : lo1.toNat ≤ hi1.toNat)
    (h₁ : hi0.toNat ≤ hi1.toNat) (s0 : Bool) : (syrkRest1 lo1 hi0 s0).toNat ≤ hi1.toNat := by
  rw [toNat_syrkRest1]; split <;> lia

private theorem order2U (u : Uplo) {nu ju ju1 : USize} (hnu : nu.toNat = n) {j : Nat}
    (hju : ju.toNat = j) (hju1 : ju1.toNat = j + 1) (hj : j + 1 < n) :
    (u.loU ju).toNat ≤ (u.loU ju1).toNat ∧ (u.loU ju1).toNat ≤ (u.hiU nu ju).toNat ∧
      (u.hiU nu ju).toNat ≤ (u.hiU nu ju1).toNat ∧ (u.hiU nu ju1).toNat ≤ n := by
  rw [u.toNat_loU, u.toNat_loU, u.toNat_hiU hnu (by lia), u.toNat_hiU hnu (by lia), hju, hju1]
  exact uplo_order2 u hj

/--
The array of `C` with the columns `j` and `j + 1` of `syrk` done. The terms `l` of the two columns
share the reads of column `l` of `A`: their common rows are updated a row of the two at a time, then
the other rows of each column, and a skipped term updates no row of its column. Each element gets
the operations of `syrkColData`, in the same order.
-/
public def syrkCol2Data (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n)
    (j : Nat) (hj : j + 1 < n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ C.data.size < USize.size ∧ n < USize.size ∧
      k < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let ku := k.toUSize
    have hku : ku.toNat = k := by grind
    let ju := j.toUSize
    have hju : ju.toNat = j := by grind
    let ju1 := (j + 1).toUSize
    have hju1 : ju1.toNat = j + 1 := by grind
    let c := C.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let cj := C.off.toUSize + C.ld.toUSize * ju
    let cj1 := C.off.toUSize + C.ld.toUSize * ju1
    let lo0 := uplo.loU ju
    let hi0 := uplo.hiU nu ju
    let lo1 := uplo.loU ju1
    let hi1 := uplo.hiU nu ju1
    have ho := order2U uplo hnu hju hju1 hj
    (inplace c do
      for i in lo0...hi0 do
        have hk : (cj + 1 * i).toNat < c.size :=
          C.toNat_col_index_lt hs.2.1 (by lia) (by lia)
        c[cj + 1 * i] := betaMul β c[cj + 1 * i]
      for i in lo1...hi1 do
        have hk : (cj1 + 1 * i).toNat < c.size :=
          C.toNat_col_index_lt hs.2.1 (by lia) (by lia)
        c[cj1 + 1 * i] := betaMul β c[cj1 + 1 * i]
      for l in 0...ku do
        let a0 := A.uget ao al rfl rfl hs.1 ju l (by lia) (by lia)
        let a1 := A.uget ao al rfl rfl hs.1 ju1 l (by lia) (by lia)
        let t0 := α * a0
        let t1 := α * a1
        let s0 := α == 0 || a0 == 0
        let s1 := α == 0 || a1 == 0
        -- Skipped rows run empty loops: an `if` would allocate a closure per term.
        let fe := syrkRows lo1 hi0 (s0 || s1)
        have hfe : fe.toNat ≤ hi0.toNat := syrkRows_le ho.2.1 _
        for i in lo1...fe do
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.1 (by lia) (by lia)
          have hk1 : (cj1 + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.1 (by lia) (by lia)
          let ail := A.uget ao al rfl rfl hs.1 i l (by lia) (by lia)
          let x0 := c[cj + 1 * i]
          let x1 := c[cj1 + 1 * i]
          c[cj + 1 * i] := x0 + t0 * ail
          c[cj1 + 1 * i] := x1 + t1 * ail
        let e0 := syrkRest0 lo0 lo1 hi0 s0 s1
        have he0 : e0.toNat ≤ hi0.toNat := syrkRest0_le (Nat.le_trans ho.1 ho.2.1) ho.2.1 _ _
        for i in lo0...e0 do
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.1 (by lia) (by lia)
          c[cj + 1 * i] := c[cj + 1 * i] + t0 * A.uget ao al rfl rfl hs.1 i l (by lia) (by lia)
        let b1 := syrkRest1 lo1 hi0 s0
        have hb1 : b1.toNat ≤ hi1.toNat :=
          syrkRest1_le (Nat.le_trans ho.2.1 ho.2.2.1) ho.2.2.1 _
        let e1 := syrkRows b1 hi1 s1
        have he1 : e1.toNat ≤ hi1.toNat := syrkRows_le hb1 _
        for i in b1...e1 do
          have hk : (cj1 + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.1 (by lia) (by lia)
          c[cj1 + 1 * i] := c[cj1 + 1 * i] + t1 * A.uget ao al rfl rfl hs.1 i l (by lia) (by lia)).2
  else mapMat C.data C.off C.ld n j (j + 2) fun i c v => syrkAt uplo α A β i c v

public theorem syrkCol2Data_eq (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n)
    (j : Nat) (hj : j + 1 < n) :
    syrkCol2Data uplo α A β C j hj =
      mapMat C.data C.off C.ld n j (j + 2) fun i c v => syrkAt uplo α A β i c v := by
  unfold syrkCol2Data
  split
  · rename_i hs
    have hnu : n.toUSize.toNat = n := by grind
    have hku : k.toUSize.toNat = k := by grind
    have hju : j.toUSize.toNat = j := by grind
    have hju1 : (j + 1).toUSize.toNat = j + 1 := by grind
    have ho := order2U uplo hnu hju hju1 hj
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v)
      (lo := uplo.loU j.toUSize) (hi := uplo.hiU n.toUSize j.toUSize) (j₀ := uplo.loU j.toUSize)
      (e := fun i => C.off.toUSize + C.ld.toUSize * j.toUSize + 1 * i)
      (idx := (Stride.mk (C.off + C.ld * j) 1).idx)
      (he := fun i _ hi => by
        rw [C.toNat_col_index hs.2.1 (by lia) (by lia), hju]; simp [Stride.idx])]
    · rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v)
        (lo := uplo.loU (j + 1).toUSize) (hi := uplo.hiU n.toUSize (j + 1).toUSize)
        (j₀ := uplo.loU (j + 1).toUSize)
        (e := fun i => C.off.toUSize + C.ld.toUSize * (j + 1).toUSize + 1 * i)
        (idx := (Stride.mk (C.off + C.ld * (j + 1)) 1).idx)
        (he := fun i _ hi => by
          rw [C.toNat_col_index hs.2.1 (by lia) (by lia), hju1]; simp [Stride.idx])]
      · rw [Tail.run_forInFrom_unit (F := syrk2Step uplo α A C.off C.ld j)
          (hF := fun _ _ => by simp [syrk2Step, size_iterRange])]
        · have hq : C.off + C.ld * (j + 1) + n ≤ C.data.size := C.col_le (by lia) hj
          simp only [Tail.run_done, USize.toNat_zero, hku, uplo.toNat_loU,
            uplo.toNat_hiU hnu (show j.toUSize.toNat < n by lia),
            uplo.toNat_hiU hnu (show (j + 1).toUSize.toNat < n by lia), hju, hju1]
          have hsc : ((C.data.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx (uplo.lo j)
                (uplo.hi n j) fun _ v => betaMul β v).modifyAt
                (Stride.mk (C.off + C.ld * (j + 1)) 1).idx (uplo.lo (j + 1)) (uplo.hi n (j + 1))
                fun _ v => betaMul β v) =
              mapMat C.data C.off C.ld n j (j + 2) fun i c v =>
                if uplo.contains i c then betaMul β v else v := by
            conv => lhs; rw [← mapMat_id C.data C.off C.ld n j (j + 2)]
            rw [modifyAt_col_mapMat_mid _ _ _ C.le_ld ⟨Nat.le_refl j, by lia⟩ (uplo.hi_le (by lia)),
              modifyAt_col_mapMat_mid _ _ _ C.le_ld ⟨by lia, by lia⟩ (uplo.hi_le (by lia))]
            apply mapMat_congr
            intro i c v hi _ _
            have e := uplo.contains_iff (j := c) hi
            have hc : c = j ∨ c = j + 1 := by lia
            simp only [e]
            rcases hc with rfl | rfl
            · by_cases h : uplo.lo c ≤ i ∧ i < uplo.hi n c <;> simp [h]
            · by_cases h : uplo.lo (j + 1) ≤ i ∧ i < uplo.hi n (j + 1) <;> simp [h]
          rw [hsc, iterRange_syrk2Step uplo α A β C.data C.off C.ld C.le_ld hj hq]
          apply mapMat_congr
          intro i c v _ _ _
          simp only [syrkAt, syrkSumAt]
        · intro l _ hl next a h
          rw [hku] at hl
          have hj0 : j.toUSize.toNat < n := by lia
          have hj1 : (j + 1).toUSize.toNat < n := by lia
          have h₀ := getElem!_pos A.data (A.off + A.ld * l.toNat + j) (A.index_lt (by lia) hl)
          have h₁ := getElem!_pos A.data (A.off + A.ld * l.toNat + (j + 1)) (A.index_lt hj hl)
          rw [Tail.run_forInFrom_unit (F := fun i t =>
              (t.set! (C.off + C.ld * j + i) (t[C.off + C.ld * j + i]! +
                α * A.data[A.off + A.ld * l.toNat + j]! * A.data[A.off + A.ld * l.toNat + i]!)).set!
                (C.off + C.ld * (j + 1) + i) (t[C.off + C.ld * (j + 1) + i]! +
                α * A.data[A.off + A.ld * l.toNat + (j + 1)]! * A.data[A.off + A.ld * l.toNat + i]!))
            (hF := fun _ _ => by simp)]
          · rw [Tail.run_forInFrom_modify
              (G := fun i v => v + α * A.data[A.off + A.ld * l.toNat + j]! *
                A.data[A.off + A.ld * l.toNat + i]!)
              (e := fun i => C.off.toUSize + C.ld.toUSize * j.toUSize + 1 * i)
              (idx := (Stride.mk (C.off + C.ld * j) 1).idx)
              (he := fun i _ hi => by
                have := syrkRest0_le (Nat.le_trans ho.1 ho.2.1) ho.2.1
                  (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 j.toUSize l hj0 hl == 0)
                  (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 (j + 1).toUSize l hj1 hl == 0)
                rw [C.toNat_col_index hs.2.1 (by lia) (by lia), hju]; simp [Stride.idx])]
            · rw [Tail.run_forInFrom_modify
                (G := fun i v => v + α * A.data[A.off + A.ld * l.toNat + (j + 1)]! *
                  A.data[A.off + A.ld * l.toNat + i]!)
                (e := fun i => C.off.toUSize + C.ld.toUSize * (j + 1).toUSize + 1 * i)
                (idx := (Stride.mk (C.off + C.ld * (j + 1)) 1).idx)
                (he := fun i _ hi => by
                  have := syrkRows_le (syrkRest1_le (Nat.le_trans ho.2.1 ho.2.2.1) ho.2.2.1
                    (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 j.toUSize l hj0 hl == 0))
                    (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 (j + 1).toUSize l hj1 hl == 0)
                  rw [C.toNat_col_index hs.2.1 (by lia) (by lia), hju1]; simp [Stride.idx])]
              · apply run_congr
                simp only [Mat.uget_eq_getElem, Mat.getElem_def, hju, hju1, ← h₀, ← h₁,
                  toNat_syrkRows, toNat_syrkRest0, toNat_syrkRest1, uplo.toNat_loU,
                  uplo.toNat_hiU hnu hj0, uplo.toNat_hiU hnu hj1]
                unfold syrk2Step
                rfl
              · intro i _ hi v
                have := syrkRows_le (syrkRest1_le (Nat.le_trans ho.2.1 ho.2.2.1) ho.2.2.1
                  (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 j.toUSize l hj0 hl == 0))
                  (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 (j + 1).toUSize l hj1 hl == 0)
                have hi' : i.toNat < n := by lia
                simp only [Mat.uget_eq_getElem, Mat.getElem_def, hju1, ← h₁,
                  getElem!_pos A.data (A.off + A.ld * l.toNat + i.toNat) (A.index_lt hi' hl)]
            · intro i _ hi v
              have := syrkRest0_le (Nat.le_trans ho.1 ho.2.1) ho.2.1
                (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 j.toUSize l hj0 hl == 0)
                (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 (j + 1).toUSize l hj1 hl == 0)
              have hi' : i.toNat < n := by lia
              simp only [Mat.uget_eq_getElem, Mat.getElem_def, hju, ← h₀,
                getElem!_pos A.data (A.off + A.ld * l.toNat + i.toNat) (A.index_lt hi' hl)]
          · intro i _ hi next' t ht
            have := syrkRows_le ho.2.1
              (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 j.toUSize l hj0 hl == 0 ||
                (α == 0 || A.uget A.off.toUSize A.ld.toUSize rfl rfl hs.1 (j + 1).toUSize l hj1 hl == 0))
            have hi' : i.toNat < n := by lia
            have p₀ := C.toNat_col_index hs.2.1 hi' hj0
            have p₁ := C.toNat_col_index hs.2.1 hi' hj1
            rw [hju, Nat.one_mul] at p₀
            rw [hju1, Nat.one_mul] at p₁
            simp only [Tail.run_readThen, Tail.run_writeThen]
            apply run_congr
            simp only [p₀, p₁, set_eq_set!, getElem_eq_getElem!, Mat.uget_eq_getElem, Mat.getElem_def,
              hju, hju1]
      · intro _ _ _ _; rfl
    · intro _ _ _ _; rfl
  · rfl

/--
The array of `syrk` from column `j` on, for a matrix with the offset `off` and the leading
dimension `ld` in the array `c` of size `sz`, two columns at a time by `syrkCol2Data`, and the
last one by `syrkColData` when `n` is odd. It takes them rather than the matrix, so that the array
isn't shared, and the column functions update it in place.
-/
public def syrkLoop (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (off ld sz : Nat)
    (hld : n ≤ ld) (hsz : n = 0 ∨ n = 0 ∨ off + ld * (n - 1) + n ≤ sz) (j : Nat)
    (c : Float32Array) (hc : c.size = sz) : Float32Array :=
  if hj2 : j + 1 < n then
    syrkLoop uplo α A β off ld sz hld hsz (j + 2)
      (syrkCol2Data uplo α A β ⟨c, off, ld, hld, by rw [hc]; exact hsz⟩ j hj2)
      (by rw [syrkCol2Data_eq, size_mapMat]; exact hc)
  else if hj : j < n then
    syrkLoop uplo α A β off ld sz hld hsz (j + 1)
      (syrkColData uplo α A β ⟨c, off, ld, hld, by rw [hc]; exact hsz⟩ j hj)
      (by rw [syrkColData_eq, size_modifyAt]; exact hc)
  else c
termination_by n - j

private theorem syrkLoop_eq (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n)
    (j : Nat) (hj : j ≤ n) (c : Float32Array) (hc : c.size = C.data.size)
    (hinv : c = mapMat C.data C.off C.ld n 0 j (syrkAt uplo α A β)) :
    syrkLoop uplo α A β C.off C.ld C.data.size C.le_ld C.bound j c hc =
      mapMat C.data C.off C.ld n 0 n (syrkAt uplo α A β) := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing j c with
  | ind e ih =>
    rw [syrkLoop]
    split
    · rename_i hj2
      refine ih (n - (j + 2)) (by lia) (j + 2) hj2 _ _ ?_ rfl
      rw [syrkCol2Data_eq]
      dsimp only
      rw [hinv]
      exact mapMat_mapMat_adj _ _ _ (Nat.zero_le j) (by lia) _
    · split
      · rename_i hj2 hjn
        refine ih (n - (j + 1)) (by lia) (j + 1) hjn _ _ ?_ rfl
        rw [syrkColData_eq]
        dsimp only
        rw [hinv]
        exact modifyAt_col_mapMat _ _ _ C.le_ld j _
      · rename_i hjn
        obtain rfl : j = n := by lia
        exact hinv

/-- The array of `syrk`. -/
public def syrkData (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n) :
    Float32Array :=
  syrkLoop uplo α A β C.off C.ld C.data.size C.le_ld C.bound 0 C.data rfl

public theorem syrkData_eq (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n) :
    syrkData uplo α A β C = mapMat C.data C.off C.ld n 0 n (syrkAt uplo α A β) :=
  syrkLoop_eq uplo α A β C 0 (Nat.zero_le _) _ rfl (mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)).symm

/--
`syrk uplo α A β C` is `α * A * Aᵀ + β * C`, on the triangle `uplo` of `C`, by the loops of the
reference BLAS: for each column `j`, it scales the triangle's part of the column by `β`, or sets it
to `0` without reading it when `β = 0`, then adds `α * A[j, l]` times column `l` of `A` to it, for
`l = 0, …, k - 1`. As in the reference BLAS, it skips the terms with `A[j, l] = 0`, so that an
infinity or a `NaN` in `A` doesn't reach them, and only scales `C` when `α = 0`. It updates `C` in
place when its array is not shared, and leaves the elements of the array outside the triangle
unchanged.
-/
@[expose] public def syrk (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n) :
    Mat n n where
  data := syrkData uplo α A β C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by rw [syrkData_eq, size_mapMat]; exact C.bound

/-- The array of `syrk uplo α A β C` is the array of `C` with its triangle updated. -/
public theorem data_syrk (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n) :
    (syrk uplo α A β C).data = mapMat C.data C.off C.ld n 0 n (syrkAt uplo α A β) :=
  syrkData_eq uplo α A β C

@[simp] public theorem off_syrk (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32)
    (C : Mat n n) : (syrk uplo α A β C).off = C.off := rfl

@[simp] public theorem ld_syrk (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32)
    (C : Mat n n) : (syrk uplo α A β C).ld = C.ld := rfl

/-- A left fold of the identity is its initial value. -/
private theorem fold_id {α : Type} (k : Nat) (x : α) : Nat.fold k (fun _ _ s => s) x = x := by
  induction k with
  | zero => rw [Nat.fold_zero]
  | succ k ih => rw [Nat.fold_succ, ih]

/--
Element `(i, j)` of `syrk uplo α A β C` in the triangle `uplo` is `betaMul β C[i, j]` when `α = 0`,
and otherwise `betaMul β C[i, j]`, plus the terms `α * A[j, l] * A[i, l]` for `l = 0, …, k - 1`,
added from the left, except those with `A[j, l] = 0`. The other elements are those of `C`.
-/
public theorem getElem_syrk (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n)
    (i j : Nat) (h : i < n ∧ j < n) :
    (syrk uplo α A β C)[(i, j)] =
      if uplo.contains i j then
        if α == 0 then betaMul β C[(i, j)]
        else Nat.fold k (fun l hl s =>
            if A[(j, l)]'⟨h.2, hl⟩ == 0 then s
            else s + α * A[(j, l)]'⟨h.2, hl⟩ * A[(i, l)]'⟨h.1, hl⟩)
          (betaMul β C[(i, j)])
      else C[(i, j)] := by
  rw [getElem_of_data_eq_mapMat _ (data_syrk uplo α A β C) rfl rfl i j h, syrkAt, syrkSumAt]
  cases hα : α == 0
  · congr 2
    funext l hl s
    rw [syrkTerm, getElem!_pos A.data _ (A.index_lt h.2 hl),
      getElem!_pos A.data _ (A.index_lt h.1 hl)]
    simp [hα, getElem_def]
  · simp only [syrkTerm, hα, Bool.true_or, ↓reduceIte, fold_id]

/-! ## Scaling a triangle -/

/-- `betaMul β` in the triangle `uplo`, and the old value elsewhere. -/
@[expose] public def scalTriAt (uplo : Uplo) (β : Float32) (i j : Nat) (v : Float32) : Float32 :=
  if uplo.contains i j then betaMul β v else v

/-- The array of `C` with its triangle `uplo` scaled by `betaMul β`. -/
public def scalTriData (uplo : Uplo) (β : Float32) (C : Mat n n) : Float32Array :=
  if hs : C.data.size < USize.size ∧ n < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let c := C.data
    let co := C.off.toUSize
    let cl := C.ld.toUSize
    (inplace c do
      for j in 0...nu do
        let cj := co + cl * j
        for i in uplo.loU j...uplo.hiU nu j do
          have hk : (cj + 1 * i).toNat < c.size :=
            C.toNat_col_index_lt hs.1 (lt_of_hiU (u := uplo) (j := j) hnu (by lia) (by lia))
              (by lia)
          c[cj + 1 * i] := betaMul β c[cj + 1 * i]).2
  else mapMat C.data C.off C.ld n 0 n (scalTriAt uplo β)

public theorem scalTriData_eq (uplo : Uplo) (β : Float32) (C : Mat n n) :
    scalTriData uplo β C = mapMat C.data C.off C.ld n 0 n (scalTriAt uplo β) := by
  unfold scalTriData
  split
  · rename_i hs
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v => scalTriAt uplo β i j v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ C.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v)
        (idx := (Stride.mk (C.off + C.ld * j.toNat) 1).idx)
        (he := fun i _ hi => C.toNat_col_index hs.1 (lt_of_hiU (u := uplo) hnu hj hi) hj)]
      · apply run_congr
        simp only [uplo.toNat_loU, uplo.toNat_hiU hnu hj]
        rw [modifyAt_widen (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (uplo.lo_le_hi hj)
          (uplo.hi_le hj)]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [scalTriAt]
        by_cases hc : uplo.contains i j.toNat = true
        · rw [ite_eq_left ((uplo.contains_iff hi).1 hc), ite_eq_left hc]
        · rw [ite_eq_right (fun h' => hc ((uplo.contains_iff hi).2 h')), ite_eq_right hc]
      · intro _ _ _ _; rfl
  · rfl

/-! ## `syrkT` -/

/-- The sum of the products `A[l, i] * A[l, j]` for `l = 0, …, k - 1`, from the left. -/
@[expose] public def syrkTSum (A : Mat k n) (i j : Nat) : Float32 :=
  Nat.fold k (fun l _ s => s + A.data[A.off + A.ld * i + l]! * A.data[A.off + A.ld * j + l]!) 0

/--
The value of the loops of `syrkT` at an element of the triangle, from the sum `t` of its products
and its old value `v`: `α * t` when `β = 0`, without reading `v`, and `α * t + β * v` otherwise.
-/
@[inline, expose] public def syrkTVal (α β t v : Float32) : Float32 :=
  if β == 0 then α * t else α * t + β * v

/-- The value of the loops of `syrkT` in the triangle `uplo`, and the old value elsewhere. -/
@[expose] public def syrkTAt (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32) (i j : Nat)
    (v : Float32) : Float32 :=
  if uplo.contains i j then syrkTVal α β (syrkTSum A i j) v else v

/-- The columns `lo` to `lo + w - 1` of `A`, as a matrix, with no copy. -/
def colsOf (A : Mat k n) (lo w : Nat) (h : lo + w ≤ n) : Mat k w where
  data := A.data
  off := A.off + A.ld * lo
  ld := A.ld
  le_ld := A.le_ld
  bound := by
    rcases A.bound with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (by lia))
    · rcases Nat.eq_zero_or_pos w with hw | hw
      · exact Or.inr (Or.inl hw)
      · have := Nat.mul_le_mul_left A.ld (show lo + (w - 1) ≤ n - 1 by lia)
        rw [Nat.mul_add] at this
        exact Or.inr (Or.inr (by lia))

/-- Column `j` of `A`, as a vector, with no copy. -/
def colVec (A : Mat k n) (j : Nat) (hj : j < n) : Vec k where
  data := A.data
  off := A.off + A.ld * j
  inc := 1
  inc_pos := Or.inl Nat.one_pos
  bound := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inl h
    · exact Or.inr (by have := A.col_le h hj; lia)

/-- The sums of `colsOf` with `colVec` are those of `syrkT`. -/
private theorem gemvTSum_colsOf (A : Mat k n) (lo w : Nat) (h : lo + w ≤ n) (j : Nat)
    (hj : j < n) (q : Nat) :
    gemvTSum (colsOf A lo w h) (colVec A j hj) q = syrkTSum A (lo + q) j := by
  simp only [gemvTSum, syrkTSum, colsOf, colVec, Nat.one_mul, Nat.mul_add, Nat.add_assoc]

/--
The sums `syrkTSum A i j` for the rows `i` of column `j` in the triangle `uplo`, from the first:
the sums of column `j` of `A` with the columns of `A` in the triangle, four at a time, by the loops
of `gemvT`.
-/
def syrkTSums (uplo : Uplo) (A : Mat k n) (hs : A.data.size < USize.size) (hk : k < USize.size)
    (hn : n < USize.size) (j : Nat) (hj : j < n) : Float32Array :=
  let lo := uplo.lo j
  let w := uplo.hi n j - lo
  have hw : lo + w ≤ n := by have := uplo.lo_le_hi hj; have := uplo.hi_le hj; lia
  gemvTSums (colsOf A lo w hw) (colVec A j hj) _ _ _ _ rfl rfl rfl rfl ⟨hs, hs⟩ (by lia)
    k.toUSize (by grind) w.toUSize (by grind) 0 (by simp) (Float32Array.emptyWithCapacity w)

theorem syrkTSums_spec (uplo : Uplo) (A : Mat k n) (hs : A.data.size < USize.size)
    (hk : k < USize.size) (hn : n < USize.size) (j : Nat) (hj : j < n) :
    (syrkTSums uplo A hs hk hn j hj).size = uplo.hi n j - uplo.lo j ∧
      ∀ q (h : q < (syrkTSums uplo A hs hk hn j hj).size),
        (syrkTSums uplo A hs hk hn j hj)[q] = syrkTSum A (uplo.lo j + q) j := by
  have hw : uplo.lo j + (uplo.hi n j - uplo.lo j) ≤ n := by
    have := uplo.lo_le_hi hj; have := uplo.hi_le hj; lia
  have := gemvTSums_spec (colsOf A (uplo.lo j) _ hw) (colVec A j hj) _ _ _ _ rfl rfl rfl rfl
    ⟨hs, hs⟩ (by lia) k.toUSize (by grind) (uplo.hi n j - uplo.lo j).toUSize (by grind) 0
    (by simp) (Float32Array.emptyWithCapacity (uplo.hi n j - uplo.lo j)) (by simp) (by simp)
  refine ⟨this.1, fun q h => ?_⟩
  rw [← gemvTSum_colsOf A _ _ hw j hj]
  exact this.2 q h

/-- The array of `syrkT`, for `α ≠ 0`. -/
public def syrkTData (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32) (C : Mat n n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ C.data.size < USize.size ∧ n < USize.size ∧
      k < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let c := C.data
    let co := C.off.toUSize
    let cl := C.ld.toUSize
    (inplace c do
      for j in 0...nu do
        let cj := co + cl * j
        let lo := uplo.loU j
        let sums := syrkTSums uplo A hs.1 hs.2.2.2 hs.2.2.1 j.toNat (by lia)
        for i in lo...uplo.hiU nu j do
          have hi : i.toNat < n := lt_of_hiU (u := uplo) (j := j) hnu (by lia) (by lia)
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.1 hi (by lia)
          c[cj + 1 * i] := syrkTVal α β sums[(i - lo).toNat]! c[cj + 1 * i]).2
  else mapMat C.data C.off C.ld n 0 n (syrkTAt uplo α A β)

public theorem syrkTData_eq (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32) (C : Mat n n) :
    syrkTData uplo α A β C = mapMat C.data C.off C.ld n 0 n (syrkTAt uplo α A β) := by
  unfold syrkTData
  split
  · rename_i hs
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v => syrkTAt uplo α A β i j v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ C.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_modify
        (G := fun i v => syrkTVal α β (syrkTSum A i j.toNat) v)
        (idx := (Stride.mk (C.off + C.ld * j.toNat) 1).idx)
        (he := fun i _ hi => C.toNat_col_index hs.2.1 (lt_of_hiU (u := uplo) hnu hj hi) hj)]
      · apply run_congr
        simp only [uplo.toNat_loU, uplo.toNat_hiU hnu hj]
        rw [modifyAt_widen (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (uplo.lo_le_hi hj)
          (uplo.hi_le hj)]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [syrkTAt]
        by_cases hc : uplo.contains i j.toNat = true
        · rw [ite_eq_left ((uplo.contains_iff hi).1 hc), ite_eq_left hc]
        · rw [ite_eq_right (fun h' => hc ((uplo.contains_iff hi).2 h')), ite_eq_right hc]
      · intro i hlo hhi v
        have hle : (uplo.loU j).toNat ≤ i.toNat := hlo
        have hsp := syrkTSums_spec uplo A hs.1 hs.2.2.2 hs.2.2.1 _ hj
        have hq : i.toNat - uplo.lo j.toNat < (syrkTSums uplo A hs.1 hs.2.2.2 hs.2.2.1 _ hj).size := by
          rw [hsp.1, ← uplo.toNat_loU, ← uplo.toNat_hiU hnu hj]; lia
        rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hle), uplo.toNat_loU,
          getElem!_pos (syrkTSums uplo A hs.1 hs.2.2.2 hs.2.2.1 _ hj) _ hq, hsp.2, Nat.add_sub_cancel' (by rw [← uplo.toNat_loU]; exact hle)]
  · rfl

/--
The value of `syrkT` in the triangle `uplo`, and the old value elsewhere, with the special cases of
the reference BLAS: `betaMul β v` when `α = 0`, and `v` when `k = 0` and `β = 1`.
-/
@[expose] public def syrkTEntryAt (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32)
    (i j : Nat) (v : Float32) : Float32 :=
  if α == 0 then scalTriAt uplo β i j v
  else if k == 0 && β == 1 then v
  else syrkTAt uplo α A β i j v

/--
`syrkT uplo α A β C` is `α * Aᵀ * A + β * C`, on the triangle `uplo` of `C`, by the loops of the
reference BLAS: for each element `(i, j)` of the triangle, it sums the products `A[l, i] * A[l, j]`
for `l = 0, …, k - 1` from the left, into `t`, then writes `α * t + β * C[i, j]`, or `α * t`
without reading `C[i, j]` when `β = 0`. It computes the sums of four elements of a column in each
pass over column `j` of `A`, by the loops of `gemvT`, which gives the same sums and lets their
additions overlap. As in the reference BLAS, it only scales `C` when `α = 0`,
and returns `C` when `k = 0` and `β = 1`. It updates `C` in place when its array is not shared,
and leaves the elements of the array outside the triangle unchanged.
-/
@[expose] public def syrkT (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32) (C : Mat n n) :
    Mat n n :=
  if α == 0 then
    { data := scalTriData uplo β C
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [scalTriData_eq, size_mapMat]; exact C.bound }
  else if k == 0 && β == 1 then C
  else
    { data := syrkTData uplo α A β C
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [syrkTData_eq, size_mapMat]; exact C.bound }

/-- The array of `syrkT uplo α A β C` is the array of `C` with its triangle updated. -/
public theorem data_syrkT (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32) (C : Mat n n) :
    (syrkT uplo α A β C).data = mapMat C.data C.off C.ld n 0 n (syrkTEntryAt uplo α A β) := by
  unfold syrkT syrkTEntryAt
  cases hα : α == 0
  · cases hq : (k == 0 && β == 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, syrkTData_eq]
    · simp only [Bool.false_eq_true, ↓reduceIte, mapMat_id]
  · simp only [↓reduceIte, scalTriData_eq]

@[simp] public theorem off_syrkT (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32)
    (C : Mat n n) : (syrkT uplo α A β C).off = C.off := by
  unfold syrkT; split
  · rfl
  · split <;> rfl

@[simp] public theorem ld_syrkT (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32)
    (C : Mat n n) : (syrkT uplo α A β C).ld = C.ld := by
  unfold syrkT; split
  · rfl
  · split <;> rfl

/--
Element `(i, j)` of `syrkT uplo α A β C` in the triangle `uplo` is `betaMul β C[i, j]` when
`α = 0`, `C[i, j]` when `k = 0` and `β = 1`, and otherwise `α * t`, when `β = 0`, or
`α * t + β * C[i, j]`, where `t` is the sum of the products `A[l, i] * A[l, j]` for
`l = 0, …, k - 1`, from the left. The other elements are those of `C`.
-/
public theorem getElem_syrkT (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32) (C : Mat n n)
    (i j : Nat) (h : i < n ∧ j < n) :
    (syrkT uplo α A β C)[(i, j)] =
      if uplo.contains i j then
        if α == 0 then betaMul β C[(i, j)]
        else if k == 0 && β == 1 then C[(i, j)]
        else
          let t := Nat.fold k (fun l hl s => s + A[(l, i)]'⟨hl, h.1⟩ * A[(l, j)]'⟨hl, h.2⟩) 0
          if β == 0 then α * t else α * t + β * C[(i, j)]
      else C[(i, j)] := by
  rw [getElem_of_data_eq_mapMat _ (data_syrkT uplo α A β C) (off_syrkT ..) (ld_syrkT ..) i j h,
    syrkTEntryAt]
  have e : syrkTSum A i j =
      Nat.fold k (fun l hl s => s + A[(l, i)]'⟨hl, h.1⟩ * A[(l, j)]'⟨hl, h.2⟩) 0 := by
    unfold syrkTSum
    congr
    funext l hl s
    rw [getElem!_pos A.data _ (A.index_lt hl h.1), getElem!_pos A.data _ (A.index_lt hl h.2)]
    rfl
  cases hα : α == 0 <;> cases hq : (k == 0 && β == 1) <;> cases hc : uplo.contains i j <;>
    simp [scalTriAt, syrkTAt, syrkTVal, hc, e]

end Mat

end BLAS.Float32
