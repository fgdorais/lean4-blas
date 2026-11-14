/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# Specifications of loops

What the kernels need beyond scalar-arrays' models of loops: `foldUpTo`, a reduction over `USize`
indices, a few element lemmas, the elements of `iterRange` loops over contiguous
windows, which the `gemm` kernels use, and the algebra of `modifyAt` at the indices of a stride.

scalar-arrays gives the models of loops, `iterRange` and `Float32Array.modifyAt`, the
`InPlace.Tail` lemmas that run a loop to them, and `Stride`, with `Stride.Fits` for a stride whose
indices are distinct and in bounds.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

/-! ## Scaling by `β` -/

/--
`β * v`, or `0` when `β = 0`, without reading `v`: the reference BLAS scales `y` or `C` by `β` this
way in `gemv` and `gemm`, so that a `NaN` or an infinity in them doesn't survive `β = 0`.
-/
@[inline, expose] public def betaMul (β v : Float32) : Float32 := if β == 0 then 0 else β * v

/-! ## Reductions -/

/--
`Nat.fold n f init`, as a loop over `USize` indices when `n < USize.size`, which holds for the size
of every array in memory, and as `Nat.fold` otherwise. It keeps a scalar `β` unboxed.

The loop runs `fu`, a version of `f` that takes the index as a `USize`, so that it can read arrays
with `uget`. A step that took a `Nat` index would convert it from `USize` and back at every element,
which costs about a third of a reduction's time. `foldUpTo_eq` needs `fu` to agree with `f`.
-/
@[specialize] public def foldUpTo {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (init : β) : β :=
  if hn : n < USize.size then loop n.toUSize (by grind) 0 init
  else Nat.fold n f init
where
  /-- The loop from the index `i`, up to the bound `m`, which is `n`. -/
  @[specialize] loop (m : USize) (hm : m.toNat = n) (i : USize) (b : β) : β :=
    if hi : i < m then loop m hm (i + 1) (fu i (hm ▸ hi) b) else b
  termination_by m.toNat - i.toNat
  decreasing_by
    grind

private theorem foldUpTo_loop_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (hf : ∀ i h b, fu i h b = f i.toNat h b)
    (m : USize) (hm : m.toNat = n) (i : USize) (k : Nat) (hk : i.toNat = k) (hkn : k ≤ n)
    (init : β) :
    foldUpTo.loop n fu m hm i (Nat.fold k (fun j hj => f j (by lia)) init) =
      Nat.fold n f init := by
  obtain ⟨d, hd⟩ : ∃ d, n - k = d := ⟨_, rfl⟩
  induction d generalizing i k with
  | zero =>
    rw [foldUpTo.loop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : k = n := by lia
    rfl
  | succ d ih =>
    have hi : i.toNat < n := by lia
    have hsucc : (i + 1).toNat = k + 1 := by grind
    rw [foldUpTo.loop, dite_eq_left_of_eq_true (eq_true (by grind)),
      hf]
    have := ih (i + 1) (k + 1) hsucc (by lia) (by lia)
    rw [Nat.fold_succ] at this
    subst hk
    exact this

public theorem foldUpTo_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (hf : ∀ i h b, fu i h b = f i.toNat h b)
    (init : β) : foldUpTo n f fu init = Nat.fold n f init := by
  unfold foldUpTo
  split
  · simpa using foldUpTo_loop_eq n f fu hf _ _ 0 0 (by simp) (by lia) init
  · rfl

/-! ## Elements -/

/-- A program that writes `v` at a `USize` index runs as one that writes it with `set!`. -/
public theorem run_set_eq_set! {N : Nat} {γ : Type} (t : InPlace.Tail N γ) (a : Float32Array)
    (i : USize) (p : Nat) (hp : i.toNat = p) (v v' : Float32) (hv : v = v') (h₁ h₂ h₃) :
    t.run (a.set i.toNat v h₁) h₂ = t.run (a.set! p v') h₃ := by
  subst hp hv
  congr 1
  simp [Float32Array.set!, h₁]

/-- A program runs the same on equal arrays. -/
public theorem run_congr {N : Nat} {γ : Type} (t : InPlace.Tail N γ) {a a' : Float32Array}
    (e : a = a') (h : a.size = N) (h' : a'.size = N) : t.run a h = t.run a' h' := by
  subst e; rfl

/-- `set` is `set!` in bounds. -/
public theorem set_eq_set! (a : Float32Array) (i : Nat) (v : Float32) (h : i < a.size) :
    a.set i v h = a.set! i v := by
  simp [Float32Array.set!, h]

/-- `getElem` is `getElem!` in bounds. -/
public theorem getElem_eq_getElem! (a : Float32Array) (i : Nat) (h : i < a.size) :
    a[i] = a[i]! := (getElem!_pos a i h).symm

/-! ## Loops of loops -/

/-- The steps of `iterRange` that keep the size of the array keep it. -/
public theorem size_iterRange (F : Nat → Float32Array → Float32Array)
    (hF : ∀ j a, (F j a).size = a.size) (lo hi : Nat) (a : Float32Array) :
    (iterRange F lo hi a).size = a.size :=
  iterRange_invariant (fun b : Float32Array => b.size = a.size)
    (fun j _ _ b hb => (hF j b).trans hb) rfl

/-- An element that no step changes is unchanged. -/
public theorem getElem!_iterRange_of_frame (F : Nat → Float32Array → Float32Array) (q : Nat)
    {lo hi : Nat} (hF : ∀ j, lo ≤ j → j < hi → ∀ a, (F j a)[q]! = a[q]!) (a : Float32Array) :
    (iterRange F lo hi a)[q]! = a[q]! := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le F (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt F (by lia), ih (fun j h₁ h₂ => hF j (by lia) h₂) _ (by lia),
      hF lo (Nat.le_refl _) (by lia)]

/--
An element that each step `F l` maps by `g l`, whatever the other elements of an array of size `N`,
ends up as the left fold of the `g l` over `l < hi`.
-/
public theorem getElem!_iterRange_of_pointwise (F : Nat → Float32Array → Float32Array) (q : Nat)
    (hi N : Nat) (g : (l : Nat) → l < hi → Float32 → Float32) (hF : ∀ j a, (F j a).size = a.size)
    (hg : ∀ l (h : l < hi) a, a.size = N → (F l a)[q]! = g l h a[q]!) (a : Float32Array)
    (ha : a.size = N) :
    (iterRange F 0 hi a)[q]! = Nat.fold hi g a[q]! := by
  induction hi with
  | zero => rw [iterRange_of_le F (Nat.le_refl _), Nat.fold_zero]
  | succ hi ih =>
    rw [iterRange_succ F (Nat.zero_le _), hg hi (by lia) _ (by rw [size_iterRange F hF, ha]),
      Nat.fold_succ, ih (fun l h => g l (by lia)) (fun l h a => hg l (by lia) a)]

/--
A step `a.set! (off + i) (G i a[off + i]!)` for each `i` in `lo ≤ i < hi` maps the elements in
the window `off + lo ≤ p < off + hi` by `G (p - off)`, and leaves the others.
-/
public theorem getElem!_iterRange_set! (off : Nat) (G : Nat → Float32 → Float32) (lo hi : Nat)
    (a : Float32Array) (p : Nat) (hp : p < a.size) :
    (iterRange (fun i a => a.set! (off + i) (G i a[off + i]!)) lo hi a)[p]! =
      if off + lo ≤ p ∧ p < off + hi then G (p - off) a[p]! else a[p]! := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    rw [iterRange_of_le _ (by lia)]
    split <;> first | rfl | lia
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), ih (lo + 1) _ (by simpa using hp) (by lia)]
    by_cases hp' : p = off + lo
    · subst hp'
      have : ¬lo + 1 ≤ lo := by lia
      simp [getElem!_pos, hp, this, show lo < hi by lia]
    · have : (a.set! (off + lo) (G lo a[off + lo]!))[p]! = a[p]! := by
        simp [getElem!_pos, hp, Ne.symm hp']
      rw [this]
      split <;> split <;> first | rfl | lia

/-- `getElem!` of `set!`, in bounds. -/
public theorem getElem!_set!_of_lt (a : Float32Array) (i : Nat) (v : Float32) {q : Nat}
    (hq : q < a.size) : (a.set! i v)[q]! = if i = q then v else a[q]! := by
  rw [getElem!_pos (a.set! i v) q (by simpa using hq), getElem!_pos a q hq,
    Float32Array.getElem_set!]

/--
A step that writes `G i a[off + i]!` at `off + i` and `G' i a[off' + i]!` at `off' + i`, for each
`i` in `lo ≤ i < hi`, in two windows that don't overlap, maps the elements of each window by its
function, and leaves the others.
-/
public theorem getElem!_iterRange_set2! (off off' : Nat) (G G' : Nat → Float32 → Float32)
    (lo hi : Nat) (hd : off + hi ≤ off') (a : Float32Array) (p : Nat) (hp : p < a.size) :
    (iterRange (fun i a => (a.set! (off + i) (G i a[off + i]!)).set! (off' + i)
        (G' i a[off' + i]!)) lo hi a)[p]! =
      if off + lo ≤ p ∧ p < off + hi then G (p - off) a[p]!
      else if off' + lo ≤ p ∧ p < off' + hi then G' (p - off') a[p]! else a[p]! := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    rw [iterRange_of_le _ (by lia)]
    split
    · lia
    · split
      · lia
      · rfl
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), ih (lo + 1) _ (by simpa using hp) (by lia)]
    have e : ∀ q, q < a.size →
        ((a.set! (off + lo) (G lo a[off + lo]!)).set! (off' + lo) (G' lo a[off' + lo]!))[q]! =
          if q = off' + lo then G' lo a[off' + lo]! else if q = off + lo then G lo a[off + lo]!
          else a[q]! := by
      intro q hq
      rw [getElem!_set!_of_lt _ _ _ (by simpa using hq), getElem!_set!_of_lt _ _ _ hq]
      have hne : off' ≠ off := by lia
      by_cases h1 : q = off' + lo
      · simp [h1]
      · by_cases h2 : q = off + lo
        · simp [h2, hne, hne.symm]
        · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    simp only [e p hp]
    by_cases h1 : p = off' + lo
    · subst h1
      simp only [show off' + lo - off' = lo by lia]
      (repeat' split) <;> first | rfl | lia
    · by_cases h2 : p = off + lo
      · subst h2
        simp only [show off + lo - off = lo by lia]
        (repeat' split) <;> first | rfl | lia
      · (repeat' split) <;> first | rfl | lia

/-! ## Updates at the indices of a stride -/

/-- `set!` of the element already there leaves the array unchanged. -/
public theorem set!_getElem!_self (a : Float32Array) (i : Nat) : a.set! i a[i]! = a := by
  apply ext_getElem (by simp)
  intro q _ _
  rw [getElem_set!]
  split
  · rename_i e; subst e; exact getElem!_pos a i (by simpa using ‹i < (a.set! i a[i]!).size›)
  · rfl

/-- `modifyAt` by the identity leaves the array unchanged. -/
public theorem modifyAt_id (a : Float32Array) (idx : Nat → Nat) (lo hi : Nat) :
    a.modifyAt idx lo hi (fun _ v => v) = a := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo with
  | zero => exact modifyAt_of_le _ _ (by lia) _
  | succ d ih => rw [modifyAt_of_lt _ _ (by lia), set!_getElem!_self, ih _ (by lia)]

/-- `modifyAt` depends only on the values of its update at the steps of its range. -/
public theorem modifyAt_congr_fun (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    {g g' : Nat → Float32 → Float32} (h : ∀ i v, lo ≤ i → i < hi → g i v = g' i v) :
    a.modifyAt idx lo hi g = a.modifyAt idx lo hi g' :=
  modifyAt_congr a (fun _ _ _ => rfl) (fun i h₁ h₂ => funext fun v => h i v h₁ h₂)

/-- Writing at the index `idx j` is `modifyAt` over the single step `j`. -/
public theorem set_eq_modifyAt (a : Float32Array) (idx : Nat → Nat) (j : Nat) (v : Float32)
    (h : idx j < a.size) : a.set (idx j) v h = a.modifyAt idx j (j + 1) fun _ _ => v := by
  rw [modifyAt_of_lt _ _ (Nat.lt_succ_self j), modifyAt_self, set_eq_set!]

/--
`modifyAt` over `lo ≤ i < hi` is `modifyAt` over a wider range, by the identity at the other
steps.
-/
public theorem modifyAt_widen (a : Float32Array) (idx : Nat → Nat) {lo hi lo' hi' : Nat}
    (g : Nat → Float32 → Float32) (h₁ : lo' ≤ lo) (h₂ : lo ≤ hi) (h₃ : hi ≤ hi') :
    a.modifyAt idx lo hi g =
      a.modifyAt idx lo' hi' fun i v => if lo ≤ i ∧ i < hi then g i v else v := by
  rw [modifyAt_split _ _ h₁ (show lo ≤ hi' by lia), modifyAt_split _ _ h₂ h₃,
    modifyAt_congr _ (lo := lo') (hi := lo) (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun i _ h => by funext v; simp [show ¬lo ≤ i by lia]),
    modifyAt_congr _ (lo := hi) (hi := hi') (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun i h _ => by funext v; simp [show ¬i < hi by lia]),
    modifyAt_congr _ (lo := lo) (hi := hi) (g := fun i v => if lo ≤ i ∧ i < hi then g i v else v)
      (g' := g) (fun _ _ _ => rfl) (fun i h₁ h₂ => by funext v; simp [h₁, h₂]),
    modifyAt_id, modifyAt_id]

/-- `modifyAt` from the step `k` of a stride is `modifyAt` on the stride from that step. -/
public theorem modifyAt_shift (a : Float32Array) (s : Stride) (k h : Nat)
    (g : Nat → Float32 → Float32) :
    a.modifyAt (s.shift k).idx 0 h g = a.modifyAt s.idx k (k + h) fun i v => g (i - k) v := by
  induction h with
  | zero => rw [modifyAt_self, Nat.add_zero, modifyAt_self]
  | succ h ih =>
    rw [modifyAt_succ _ _ (Nat.zero_le _), ← Nat.add_assoc, modifyAt_succ _ _ (by lia), ← ih,
      Stride.idx_shift, Nat.add_sub_cancel_left]

/-- The steps of a stride that fits are at distinct indices. -/
public theorem _root_.ScalarArray.Stride.Fits.injOn {s : Stride} {N size : Nat} (hs : s.Fits N size) {lo hi : Nat}
    (hn : hi ≤ N) : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → s.idx i = s.idx j → i = j :=
  fun _ _ h₁ _ _ h₂ e => hs.idx_inj (by lia) (by lia) e

/--
Two `modifyAt` at the same indices, distinct and in bounds, compose: the element at the step `i`
is mapped by `g i` and then `g' i`.
-/
public theorem modifyAt_modifyAt (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    (hinj : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → idx i = idx j → i = j)
    (g g' : Nat → Float32 → Float32) :
    (a.modifyAt idx lo hi g).modifyAt idx lo hi g' = a.modifyAt idx lo hi fun i v => g' i (g i v) := by
  apply ext_getElem (by simp)
  intro p hp _
  by_cases hc : ∃ i, lo ≤ i ∧ i < hi ∧ idx i = p
  · obtain ⟨i, h₁, h₂, rfl⟩ := hc
    rw [getElem_modifyAt_idx _ _ _ hinj h₁ h₂ hp, getElem_modifyAt_idx _ _ _ hinj h₁ h₂,
      getElem_modifyAt_idx _ _ _ hinj h₁ h₂]
  · have hne : ∀ i, lo ≤ i → i < hi → idx i ≠ p := fun i h₁ h₂ e => hc ⟨i, h₁, h₂, e⟩
    rw [getElem_modifyAt_of_forall_ne _ _ _ hne hp, getElem_modifyAt_of_forall_ne _ _ _ hne,
      getElem_modifyAt_of_forall_ne _ _ _ hne]

/--
Steps that each `modifyAt` the same indices, distinct and in bounds, by `G j` at step `j`, map
them by the left fold of the `G j` over `j < n`.
-/
public theorem iterRange_modifyAt (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    (hinj : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → idx i = idx j → i = j) (n : Nat)
    (G : Nat → Nat → Float32 → Float32) :
    iterRange (fun j c => c.modifyAt idx lo hi (G j)) 0 n a =
      a.modifyAt idx lo hi fun i v => Nat.fold n (fun j _ v => G j i v) v := by
  induction n with
  | zero =>
    rw [iterRange_self, modifyAt_congr a (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext v; simp), modifyAt_id]
  | succ n ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih, modifyAt_modifyAt _ _ hinj]
    simp only [Nat.fold_succ]

/--
Writing `t` at the step `j` of a stride, then updating the steps from `j + 1` to `n - 1` by `G`,
as the steps of the stride from `j + 1`, is a `modifyAt` over the steps `j ≤ i < n`: the
triangular update.
-/
public theorem set_modifyAt_succ (a : Float32Array) (s : Stride) {j n : Nat} (t : Float32)
    (G : Nat → Float32 → Float32) (hj : j < n) (p : Nat) (hp : p = s.idx j) (h : p < a.size) :
    (a.set p t h).modifyAt (s.shift (j + 1)).idx 0 (n - j - 1) G =
      a.modifyAt s.idx j n fun i v => if i = j then t else G (i - (j + 1)) v := by
  subst hp
  rw [set_eq_modifyAt a s.idx j t, modifyAt_shift, show j + 1 + (n - j - 1) = n by lia,
    modifyAt_split a s.idx (Nat.le_succ j) (show j + 1 ≤ n by lia)]
  have e : a.modifyAt s.idx j (j + 1) (fun i v => if i = j then t else G (i - (j + 1)) v) =
      a.modifyAt s.idx j (j + 1) fun _ _ => t :=
    modifyAt_congr _ (fun _ _ _ => rfl) (fun i h₁ h₂ => by funext v; simp [show i = j by lia])
  rw [e]
  exact modifyAt_congr _ (fun _ _ _ => rfl) (fun i h₁ _ => by
    funext v; simp [show i ≠ j by lia])

/--
Writing `t` at the step `j` of a stride that fits, then updating the steps before `j` by `G`, is a
`modifyAt` over the steps `i ≤ j`: the triangular update from the end.
-/
public theorem set_modifyAt_pred (a : Float32Array) {s : Stride} {N : Nat}
    (hs : s.Fits N a.size) {j : Nat} (hj : j < N) (t : Float32) (G : Nat → Float32 → Float32)
    (p : Nat) (hp : p = s.idx j) (h : p < a.size) :
    (a.set p t h).modifyAt s.idx 0 j G =
      a.modifyAt s.idx 0 (j + 1) fun i v => if i = j then t else G i v := by
  subst hp
  rw [modifyAt_succ_of_injOn _ _ (Nat.zero_le _) _ (hs.injOn hj), set_eq_set!]
  simp only [↓reduceIte]
  exact modifyAt_congr _ (fun _ _ _ => rfl) (fun i _ h₂ => by
    funext v; simp [show i ≠ j by lia])

end BLAS.Float32
