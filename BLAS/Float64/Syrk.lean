/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Trsv
import all BLAS.Internal

/-!
# Symmetric rank-k update

`Mat.syrk uplo α A β C` is `α * A * Aᵀ + β * C` and `Mat.syrkT uplo α A β C` is
`α * Aᵀ * A + β * C`, on the triangle `uplo` of `C`, by the loops of the reference BLAS. Each
element gets the operations of those loops, in the same order, with the special cases of the
reference BLAS: `syrk` skips the terms with `A[j, l] = 0`, both only scale `C` when `α = 0`, and
`syrkT` leaves `C` unchanged when `k = 0` and `β = 1`.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

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
@[expose] public def syrkTerm (α : Float) (A : Mat n k) (l i j : Nat) (s : Float) : Float :=
  if α == 0 || A.data[A.off + A.ld * l + j]! == 0 then s
  else s + α * A.data[A.off + A.ld * l + j]! * A.data[A.off + A.ld * l + i]!

/--
The value of the loops of `syrk` at `(i, j)` of the triangle, from its old value `v`, on the arrays:
`betaMul β v`, plus the terms `syrkTerm α A l i j` for `l = 0, …, k - 1`, from the left.
-/
@[expose] public def syrkSumAt (α : Float) (A : Mat n k) (β : Float) (i j : Nat) (v : Float) :
    Float :=
  Nat.fold k (fun l _ s => syrkTerm α A l i j s) (betaMul β v)

/-- `syrkSumAt` in the triangle `uplo`, and the old value elsewhere. -/
@[expose] public def syrkAt (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (i j : Nat)
    (v : Float) : Float :=
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
public def syrkColData (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n)
    (j : Nat) (hj : j < n) : Float64Array :=
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

public theorem syrkColData_eq (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n)
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

/--
The array of `syrk` from column `j` on, for a matrix with the offset `off` and the leading
dimension `ld` in the array `c` of size `sz`. It takes them rather than the matrix, so that the
array isn't shared, and `syrkColData` updates it in place.
-/
public def syrkLoop (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (off ld sz : Nat)
    (hld : n ≤ ld) (hsz : n = 0 ∨ n = 0 ∨ off + ld * (n - 1) + n ≤ sz) (j : Nat)
    (c : Float64Array) (hc : c.size = sz) : Float64Array :=
  if hj : j < n then
    syrkLoop uplo α A β off ld sz hld hsz (j + 1)
      (syrkColData uplo α A β ⟨c, off, ld, hld, by rw [hc]; exact hsz⟩ j hj)
      (by rw [syrkColData_eq, size_modifyAt]; exact hc)
  else c
termination_by n - j

private theorem syrkLoop_eq (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n)
    (j : Nat) (hj : j ≤ n) (c : Float64Array) (hc : c.size = C.data.size)
    (hinv : c = mapMat C.data C.off C.ld n 0 j (syrkAt uplo α A β)) :
    syrkLoop uplo α A β C.off C.ld C.data.size C.le_ld C.bound j c hc =
      mapMat C.data C.off C.ld n 0 n (syrkAt uplo α A β) := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e generalizing j c with
  | zero =>
    obtain rfl : j = n := by lia
    rw [syrkLoop, dite_eq_right (Nat.lt_irrefl _), hinv]
  | succ e ih =>
    have hjn : j < n := by lia
    rw [syrkLoop, dite_eq_left hjn]
    refine ih (j + 1) hjn _ _ ?_ (by lia)
    rw [syrkColData_eq]
    dsimp only
    rw [hinv]
    exact modifyAt_col_mapMat _ _ _ C.le_ld j _

/-- The array of `syrk`. -/
public def syrkData (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n) :
    Float64Array :=
  syrkLoop uplo α A β C.off C.ld C.data.size C.le_ld C.bound 0 C.data rfl

public theorem syrkData_eq (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n) :
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
@[expose] public def syrk (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n) :
    Mat n n where
  data := syrkData uplo α A β C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by rw [syrkData_eq, size_mapMat]; exact C.bound

/-- The array of `syrk uplo α A β C` is the array of `C` with its triangle updated. -/
public theorem data_syrk (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n) :
    (syrk uplo α A β C).data = mapMat C.data C.off C.ld n 0 n (syrkAt uplo α A β) :=
  syrkData_eq uplo α A β C

@[simp] public theorem off_syrk (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float)
    (C : Mat n n) : (syrk uplo α A β C).off = C.off := rfl

@[simp] public theorem ld_syrk (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float)
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
public theorem getElem_syrk (uplo : Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n)
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
@[expose] public def scalTriAt (uplo : Uplo) (β : Float) (i j : Nat) (v : Float) : Float :=
  if uplo.contains i j then betaMul β v else v

/-- The array of `C` with its triangle `uplo` scaled by `betaMul β`. -/
public def scalTriData (uplo : Uplo) (β : Float) (C : Mat n n) : Float64Array :=
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

public theorem scalTriData_eq (uplo : Uplo) (β : Float) (C : Mat n n) :
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
@[expose] public def syrkTSum (A : Mat k n) (i j : Nat) : Float :=
  Nat.fold k (fun l _ s => s + A.data[A.off + A.ld * i + l]! * A.data[A.off + A.ld * j + l]!) 0

/--
The value of the loops of `syrkT` at an element of the triangle, from the sum `t` of its products
and its old value `v`: `α * t` when `β = 0`, without reading `v`, and `α * t + β * v` otherwise.
-/
@[inline, expose] public def syrkTVal (α β t v : Float) : Float :=
  if β == 0 then α * t else α * t + β * v

/-- The value of the loops of `syrkT` in the triangle `uplo`, and the old value elsewhere. -/
@[expose] public def syrkTAt (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float) (i j : Nat)
    (v : Float) : Float :=
  if uplo.contains i j then syrkTVal α β (syrkTSum A i j) v else v

/-- `syrkTSum A i j` on `USize` indices, as a loop. -/
@[inline] public def syrkTDot (A : Mat k n) (ao al : USize) (ha : A.off.toUSize = ao)
    (hl : A.ld.toUSize = al) (hs : A.data.size < USize.size) (i j : USize) (hi : i.toNat < n)
    (hj : j.toNat < n) : Float :=
  foldUpTo k (fun l _ s => s + A.data[A.off + A.ld * i.toNat + l]! *
      A.data[A.off + A.ld * j.toNat + l]!)
    (fun l hl' s => s + A.uget ao al ha hl hs l i hl' hi * A.uget ao al ha hl hs l j hl' hj) 0

public theorem syrkTDot_eq (A : Mat k n) (ao al : USize) (ha : A.off.toUSize = ao)
    (hl : A.ld.toUSize = al) (hs : A.data.size < USize.size) (i j : USize) (hi : i.toNat < n)
    (hj : j.toNat < n) : syrkTDot A ao al ha hl hs i j hi hj = syrkTSum A i.toNat j.toNat := by
  unfold syrkTDot syrkTSum
  rw [foldUpTo_eq]
  intro l hl' s
  rw [Mat.uget_eq_getElem, Mat.uget_eq_getElem, getElem_def, getElem_def,
    getElem!_pos A.data _ (A.index_lt hl' hi), getElem!_pos A.data _ (A.index_lt hl' hj)]

/-- The array of `syrkT`, for `α ≠ 0`. -/
public def syrkTData (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float) (C : Mat n n) :
    Float64Array :=
  if hs : A.data.size < USize.size ∧ C.data.size < USize.size ∧ n < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let c := C.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let co := C.off.toUSize
    let cl := C.ld.toUSize
    (inplace c do
      for j in 0...nu do
        let cj := co + cl * j
        for i in uplo.loU j...uplo.hiU nu j do
          have hi : i.toNat < n := lt_of_hiU (u := uplo) (j := j) hnu (by lia) (by lia)
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.1 hi (by lia)
          c[cj + 1 * i] :=
            syrkTVal α β (syrkTDot A ao al rfl rfl hs.1 i j hi (by lia)) c[cj + 1 * i]).2
  else mapMat C.data C.off C.ld n 0 n (syrkTAt uplo α A β)

public theorem syrkTData_eq (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float) (C : Mat n n) :
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
      · intro i _ _ v
        rw [syrkTDot_eq]
  · rfl

/--
The value of `syrkT` in the triangle `uplo`, and the old value elsewhere, with the special cases of
the reference BLAS: `betaMul β v` when `α = 0`, and `v` when `k = 0` and `β = 1`.
-/
@[expose] public def syrkTEntryAt (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float)
    (i j : Nat) (v : Float) : Float :=
  if α == 0 then scalTriAt uplo β i j v
  else if k == 0 && β == 1 then v
  else syrkTAt uplo α A β i j v

/--
`syrkT uplo α A β C` is `α * Aᵀ * A + β * C`, on the triangle `uplo` of `C`, by the loops of the
reference BLAS: for each element `(i, j)` of the triangle, it sums the products `A[l, i] * A[l, j]`
for `l = 0, …, k - 1` from the left, into `t`, then writes `α * t + β * C[i, j]`, or `α * t`
without reading `C[i, j]` when `β = 0`. As in the reference BLAS, it only scales `C` when `α = 0`,
and returns `C` when `k = 0` and `β = 1`. It updates `C` in place when its array is not shared,
and leaves the elements of the array outside the triangle unchanged.
-/
@[expose] public def syrkT (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float) (C : Mat n n) :
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
public theorem data_syrkT (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float) (C : Mat n n) :
    (syrkT uplo α A β C).data = mapMat C.data C.off C.ld n 0 n (syrkTEntryAt uplo α A β) := by
  unfold syrkT syrkTEntryAt
  cases hα : α == 0
  · cases hq : (k == 0 && β == 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, syrkTData_eq]
    · simp only [Bool.false_eq_true, ↓reduceIte, mapMat_id]
  · simp only [↓reduceIte, scalTriData_eq]

@[simp] public theorem off_syrkT (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float)
    (C : Mat n n) : (syrkT uplo α A β C).off = C.off := by
  unfold syrkT; split
  · rfl
  · split <;> rfl

@[simp] public theorem ld_syrkT (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float)
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
public theorem getElem_syrkT (uplo : Uplo) (α : Float) (A : Mat k n) (β : Float) (C : Mat n n)
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

end BLAS.Float64
