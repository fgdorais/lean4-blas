/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# Specifications of loops

The models of the loops that the `inplace` notation compiles to, with the lemmas that run them.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

/-- The array `a` with `g i a[i]` at the indices `lo ≤ i < hi`. -/
public def mapRange (a : Float64Array) (lo hi : Nat) (g : Nat → Float → Float) : Float64Array :=
  .ofFn (n := a.size) fun i => if lo ≤ i.val ∧ i.val < hi then g i.val a[i.val] else a[i.val]

@[simp] public theorem size_mapRange (a : Float64Array) (lo hi g) :
    (mapRange a lo hi g).size = a.size := by
  simp [mapRange]

@[simp] public theorem getElem_mapRange (a : Float64Array) (lo hi g i)
    (h : i < (mapRange a lo hi g).size) :
    (mapRange a lo hi g)[i] =
      if lo ≤ i ∧ i < hi then g i (a[i]'(by simpa using h)) else a[i]'(by simpa using h) := by
  simp [mapRange]

public theorem mapRange_of_le (a : Float64Array) (lo hi g) (h : hi ≤ lo) :
    mapRange a lo hi g = a := by
  apply ext_getElem (by simp)
  intro i _ _
  simp only [mapRange, getElem_ofFn]
  split
  · omega
  · rfl

/--
Runs a loop that replaces each element `a[j]`, for `j₀ ≤ j < hi`, with `g j a[j]`, where `g`
may use the bound of `j`, and then runs `k`. It is the loop of
`for j in 0...hi do a[j] := e`, from step `j₀`, for a term `e` that reads only `a[j]`.
-/
public theorem run_forInFrom_map {n : Nat} {γ : Type} (hi j₀ : USize)
    (hlo : (0 : USize).toNat ≤ j₀.toNat)
    (g : (j : USize) → j.toNat < hi.toNat → Float → Float) (G : Nat → Float → Float)
    (hg : ∀ j hj v, g j hj v = G j.toNat v)
    (p : ∀ j : USize, j.toNat < hi.toNat → j.toNat < n) (k : Unit → Tail n γ)
    (a : Float64Array) (h : a.size = n) :
    (Tail.forInFrom 0 hi j₀ hlo ()
        (fun j _ hj next _ => Tail.readThen j (p j hj) fun v =>
          Tail.writeThen j (p j hj) (g j hj v) (next ())) k).run a h =
      (k ()).run (mapRange a j₀.toNat hi.toNat G) (by simp [h]) := by
  obtain ⟨d, hd⟩ : ∃ d, hi.toNat - j₀.toNat = d := ⟨_, rfl⟩
  induction d generalizing j₀ a with
  | zero =>
    have hj : ¬ j₀ < hi := by rw [USize.lt_iff_toNat_lt]; omega
    rw [Tail.forInFrom_eq, dite_eq_right_of_eq_false (eq_false hj)]
    congr 1
    exact (mapRange_of_le a _ _ G (by omega)).symm
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; omega
    have hj' : j₀.toNat < hi.toNat := hj
    rw [Tail.forInFrom_eq, dite_eq_left_of_eq_true (eq_true hj)]
    simp only [Tail.run_readThen, Tail.run_writeThen]
    have hsucc : (j₀ + 1).toNat = j₀.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt]
      have : hi.toNat < USize.size := hi.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      omega
    rw [ih (j₀ + 1) _ _ _ (by rw [hsucc]; omega)]
    congr 1
    apply ext_getElem (by simp)
    intro i _ _
    simp only [mapRange, getElem_ofFn, getElem_set, hsucc]
    by_cases hij : j₀.toNat = i
    · subst hij
      simp [hj', Nat.not_succ_le_self]
      exact hg _ _ _
    · simp only [hij, ite_false]
      split <;> split <;> first | rfl | omega

/-! ## Reductions -/

/--
`Nat.fold n f init`, as a loop over `USize` indices when `n < USize.size`, which holds for the size
of every array in memory, and as `Nat.fold` otherwise. It keeps a scalar `β` unboxed.
-/
@[specialize] public def foldUpTo {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (init : β) : β :=
  if hn : n < USize.size then loop hn 0 init else Nat.fold n f init
where
  /-- The loop from the index `i`. -/
  @[specialize] loop (hn : n < USize.size) (i : USize) (b : β) : β :=
    if hi : i.toNat < n then loop hn (i + 1) (f i.toNat hi b) else b
  termination_by n - i.toNat
  decreasing_by
    have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
    rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem foldUpTo_loop_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (hn : n < USize.size) (i : USize) (k : Nat) (hk : i.toNat = k) (hkn : k ≤ n) (init : β) :
    foldUpTo.loop n f hn i (Nat.fold k (fun j hj => f j (by omega)) init) =
      Nat.fold n f init := by
  obtain ⟨d, hd⟩ : ∃ d, n - k = d := ⟨_, rfl⟩
  induction d generalizing i k with
  | zero =>
    rw [foldUpTo.loop, dite_eq_right_of_eq_false (eq_false (by omega))]
    obtain rfl : k = n := by omega
    rfl
  | succ d ih =>
    have hi : i.toNat < n := by omega
    have hsucc : (i + 1).toNat = k + 1 := by
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega), hk]
    rw [foldUpTo.loop, dite_eq_left_of_eq_true (eq_true hi)]
    have := ih (i + 1) (k + 1) hsucc (by omega) (by omega)
    rw [Nat.fold_succ] at this
    subst hk
    exact this

public theorem foldUpTo_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β) (init : β) :
    foldUpTo n f init = Nat.fold n f init := by
  unfold foldUpTo
  split
  · rename_i hn
    simpa using foldUpTo_loop_eq n f hn 0 0 (by simp) (by omega) init
  · rfl

end BLAS.Float64
