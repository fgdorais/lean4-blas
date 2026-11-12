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
  · lia
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
    have hj : ¬ j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    rw [Tail.forInFrom_eq, dite_eq_right_of_eq_false (eq_false hj)]
    congr 1
    exact (mapRange_of_le a _ _ G (by lia)).symm
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    have hj' : j₀.toNat < hi.toNat := hj
    rw [Tail.forInFrom_eq, dite_eq_left_of_eq_true (eq_true hj)]
    simp only [Tail.run_readThen, Tail.run_writeThen]
    have hsucc : (j₀ + 1).toNat = j₀.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt]
      have : hi.toNat < USize.size := hi.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      lia
    rw [ih (j₀ + 1) _ _ _ (by rw [hsucc]; lia)]
    congr 1
    apply ext_getElem (by simp)
    intro i _ _
    simp only [mapRange, getElem_ofFn, getElem_set, hsucc]
    by_cases hij : j₀.toNat = i
    · subst hij
      simp [hj', Nat.not_succ_le_self]
      exact hg _ _ _
    · simp only [hij, ite_false]
      split <;> split <;> first | rfl | lia

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
  if hn : n < USize.size then loop n.toUSize (by simp [Nat.mod_eq_of_lt hn]) 0 init
  else Nat.fold n f init
where
  /-- The loop from the index `i`, up to the bound `m`, which is `n`. -/
  @[specialize] loop (m : USize) (hm : m.toNat = n) (i : USize) (b : β) : β :=
    if hi : i < m then loop m hm (i + 1) (fu i (hm ▸ hi) b) else b
  termination_by m.toNat - i.toNat
  decreasing_by
    rw [USize.lt_iff_toNat_lt] at hi
    have : m.toNat < USize.size := m.toNat_lt_size
    have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
    rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by lia)]
    lia

private theorem foldUpTo_loop_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (hf : ∀ i h b, fu i h b = f i.toNat h b)
    (m : USize) (hm : m.toNat = n) (i : USize) (k : Nat) (hk : i.toNat = k) (hkn : k ≤ n)
    (init : β) :
    foldUpTo.loop n fu m hm i (Nat.fold k (fun j hj => f j (by lia)) init) =
      Nat.fold n f init := by
  obtain ⟨d, hd⟩ : ∃ d, n - k = d := ⟨_, rfl⟩
  induction d generalizing i k with
  | zero =>
    rw [foldUpTo.loop, dite_eq_right_of_eq_false (eq_false (by rw [USize.lt_iff_toNat_lt]; lia))]
    obtain rfl : k = n := by lia
    rfl
  | succ d ih =>
    have hi : i.toNat < n := by lia
    have hsucc : (i + 1).toNat = k + 1 := by
      have : m.toNat < USize.size := m.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by lia), hk]
    rw [foldUpTo.loop, dite_eq_left_of_eq_true (eq_true (by rw [USize.lt_iff_toNat_lt]; lia)),
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

/-! ## Indices -/

/-- `(x + y).toNat = x.toNat + y.toNat` when the sum doesn't wrap around. -/
public theorem USize.toNat_add_of_lt {x y : USize} (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by lia)]

/-- `(x * y).toNat = x.toNat * y.toNat` when the product doesn't wrap around. -/
public theorem USize.toNat_mul_of_lt {x y : USize} (h : x.toNat * y.toNat < USize.size) :
    (x * y).toNat = x.toNat * y.toNat := by
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_mul, Nat.mod_eq_of_lt (by lia)]

/-- A program that writes `v` at a `USize` index runs as one that writes it with `set!`. -/
public theorem Tail.run_set_eq_set! {N : Nat} {γ : Type} (t : InPlace.Tail N γ) (a : Float64Array)
    (i : USize) (p : Nat) (hp : i.toNat = p) (v v' : Float) (hv : v = v') (h₁ h₂ h₃) :
    t.run (a.set i.toNat v h₁) h₂ = t.run (a.set! p v') h₃ := by
  subst hp hv
  congr 1
  simp [Float64Array.set!, h₁]

/-- A program runs the same on equal arrays. -/
public theorem Tail.run_congr {N : Nat} {γ : Type} (t : InPlace.Tail N γ) {a a' : Float64Array}
    (e : a = a') (h : a.size = N) (h' : a'.size = N) : t.run a h = t.run a' h' := by
  subst e; rfl

/-- `set` is `set!` in bounds. -/
public theorem Float64Array.set_eq_set! (a : Float64Array) (i : Nat) (v : Float) (h : i < a.size) :
    a.set i v h = a.set! i v := by
  simp [Float64Array.set!, h]

/-- `getElem` is `getElem!` in bounds. -/
public theorem Float64Array.getElem_eq_getElem! (a : Float64Array) (i : Nat) (h : i < a.size) :
    a[i] = a[i]! := (getElem!_pos a i h).symm

/-! ## Loops of loops -/

/--
`iterRange F lo hi a` runs the steps `F lo`, `F (lo + 1)`, …, `F (hi - 1)` on `a`, in this order.
It is the model of a loop whose body runs a program, such as another loop, on the array.
-/
public def iterRange (F : Nat → Float64Array → Float64Array) (lo hi : Nat) (a : Float64Array) :
    Float64Array :=
  if lo < hi then iterRange F (lo + 1) hi (F lo a) else a
termination_by hi - lo

public theorem iterRange_of_lt (F : Nat → Float64Array → Float64Array) {lo hi : Nat} (h : lo < hi)
    (a : Float64Array) : iterRange F lo hi a = iterRange F (lo + 1) hi (F lo a) := by
  rw [iterRange]; simp [h]

public theorem iterRange_of_le (F : Nat → Float64Array → Float64Array) {lo hi : Nat} (h : hi ≤ lo)
    (a : Float64Array) : iterRange F lo hi a = a := by
  rw [iterRange]; simp [show ¬lo < hi by lia]

public theorem size_iterRange (F : Nat → Float64Array → Float64Array)
    (hF : ∀ j a, (F j a).size = a.size) (lo hi : Nat) (a : Float64Array) :
    (iterRange F lo hi a).size = a.size := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le F (by lia)]
  | succ d ih => rw [iterRange_of_lt F (by lia), ih (lo + 1) _ (by lia), hF]

/-- The last step of `iterRange` comes last. -/
public theorem iterRange_succ (F : Nat → Float64Array → Float64Array) {lo hi : Nat} (h : lo ≤ hi)
    (a : Float64Array) : iterRange F lo (hi + 1) a = F hi (iterRange F lo hi a) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    obtain rfl : lo = hi := by lia
    rw [iterRange_of_lt F (by lia), iterRange_of_le F (by lia), iterRange_of_le F (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt F (show lo < hi + 1 by lia), ih (lo := lo + 1) (by lia) _ (by lia),
      ← iterRange_of_lt F (show lo < hi by lia)]

/-- `iterRange` splits at any `mid` between its bounds. -/
public theorem iterRange_split (F : Nat → Float64Array → Float64Array) {lo mid hi : Nat}
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (a : Float64Array) :
    iterRange F lo hi a = iterRange F mid hi (iterRange F lo mid a) := by
  obtain ⟨d, hd⟩ : ∃ d, mid - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    obtain rfl : lo = mid := by lia
    rw [iterRange_of_le F (Nat.le_refl _)]
  | succ d ih =>
    rw [iterRange_of_lt F (show lo < hi by lia), iterRange_of_lt F (show lo < mid by lia),
      ih (by lia) _ (by lia)]

/-- An element that no step changes is unchanged. -/
public theorem getElem!_iterRange_of_frame (F : Nat → Float64Array → Float64Array) (q : Nat)
    {lo hi : Nat} (hF : ∀ j, lo ≤ j → j < hi → ∀ a, (F j a)[q]! = a[q]!) (a : Float64Array) :
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
public theorem getElem!_iterRange_of_pointwise (F : Nat → Float64Array → Float64Array) (q : Nat)
    (hi N : Nat) (g : (l : Nat) → l < hi → Float → Float) (hF : ∀ j a, (F j a).size = a.size)
    (hg : ∀ l (h : l < hi) a, a.size = N → (F l a)[q]! = g l h a[q]!) (a : Float64Array)
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
public theorem getElem!_iterRange_set! (off : Nat) (G : Nat → Float → Float) (lo hi : Nat)
    (a : Float64Array) (p : Nat) (hp : p < a.size) :
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
public theorem getElem!_set!_of_lt (a : Float64Array) (i : Nat) (v : Float) {q : Nat}
    (hq : q < a.size) : (a.set! i v)[q]! = if i = q then v else a[q]! := by
  rw [getElem!_pos (a.set! i v) q (by simpa using hq), getElem!_pos a q hq,
    Float64Array.getElem_set!]

/--
A step that writes `G i a[off + i]!` at `off + i` and `G' i a[off' + i]!` at `off' + i`, for each
`i` in `lo ≤ i < hi`, in two windows that don't overlap, maps the elements of each window by its
function, and leaves the others.
-/
public theorem getElem!_iterRange_set2! (off off' : Nat) (G G' : Nat → Float → Float)
    (lo hi : Nat) (hd : off + hi ≤ off') (a : Float64Array) (p : Nat) (hp : p < a.size) :
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

/--
Runs a loop whose body runs a program that maps the array by `F j` and then runs the next step,
from the step `j₀`, and then runs `k`: it maps the array by `iterRange F j₀ hi`.
-/
public theorem run_forInFrom_iter {n : Nat} {γ : Type} (lo hi j₀ : USize)
    (hlo : lo.toNat ≤ j₀.toNat)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (Unit → Tail n γ) → Unit → Tail n γ)
    (F : Nat → Float64Array → Float64Array) (hF : ∀ j a, (F j a).size = a.size)
    (hbody : ∀ j hl hj next a (h : a.size = n),
      (body j hl hj next ()).run a h = (next ()).run (F j.toNat a) (by rw [hF]; exact h))
    (k : Unit → Tail n γ) (a : Float64Array) (h : a.size = n) :
    (Tail.forInFrom lo hi j₀ hlo () body k).run a h =
      (k ()).run (iterRange F j₀.toNat hi.toNat a) (by rw [size_iterRange F hF]; exact h) := by
  obtain ⟨d, hd⟩ : ∃ d, hi.toNat - j₀.toNat = d := ⟨_, rfl⟩
  induction d generalizing j₀ a with
  | zero =>
    have hj : ¬ j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    rw [Tail.forInFrom_eq, dite_eq_right_of_eq_false (eq_false hj)]
    congr 1
    exact (iterRange_of_le F (by lia) a).symm
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    have hj' : j₀.toNat < hi.toNat := hj
    rw [Tail.forInFrom_eq, dite_eq_left_of_eq_true (eq_true hj)]
    refine Eq.trans (hbody j₀ hlo hj' _ a h) ?_
    have hsucc : (j₀ + 1).toNat = j₀.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt]
      have : hi.toNat < USize.size := hi.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      lia
    rw [ih (j₀ + 1) _ _ _ (by rw [hsucc]; lia)]
    congr 1
    rw [hsucc, iterRange_of_lt F hj']

/-! ## Strides -/

/--
The array `a` with `g i a[off + inc * i]` at the indices `off + inc * i`, for `lo ≤ i < hi`. For
`inc = 0`, only the index `off`, for `i = 0`, is changed.
-/
@[expose] public def mapStride (a : Float64Array) (off inc lo hi : Nat) (g : Nat → Float → Float) :
    Float64Array :=
  .ofFn (n := a.size) fun p =>
    if off ≤ p.val ∧ (p.val - off) % inc = 0 ∧ lo ≤ (p.val - off) / inc ∧ (p.val - off) / inc < hi
    then g ((p.val - off) / inc) a[p.val] else a[p.val]

@[simp] public theorem size_mapStride (a : Float64Array) (off inc lo hi g) :
    (mapStride a off inc lo hi g).size = a.size := by
  simp [mapStride]

/-- The index `off + inc * i` of a stride is the step `i`, for `inc > 0` or `i = 0`. -/
theorem stride_index {off inc i : Nat} (h : 0 < inc ∨ i = 0) :
    off ≤ off + inc * i ∧ (off + inc * i - off) % inc = 0 ∧ (off + inc * i - off) / inc = i := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [Nat.add_sub_cancel_left]
  rcases h with h | rfl
  · exact ⟨Nat.mul_mod_right _ _, Nat.mul_div_cancel_left _ h⟩
  · simp

/-- An index `p ≥ off` with `(p - off) % inc = 0` is `off + inc * ((p - off) / inc)`. -/
theorem eq_stride_of_mod {off inc p : Nat} (h₁ : off ≤ p) (h₂ : (p - off) % inc = 0) :
    p = off + inc * ((p - off) / inc) := by
  have := Nat.mod_add_div (p - off) inc
  lia

/-- The element of a stride. -/
public theorem getElem_mapStride_stride (a : Float64Array) (off inc lo hi g) {i : Nat}
    (hr : lo ≤ i ∧ i < hi) (hinc : 0 < inc ∨ i = 0) (h : off + inc * i < a.size) :
    (mapStride a off inc lo hi g)[off + inc * i]'(by simpa using h) = g i a[off + inc * i] := by
  obtain ⟨h₁, h₂, h₃⟩ := stride_index (off := off) hinc
  simp only [mapStride, getElem_ofFn]
  rw [ite_eq_left (by rw [h₃]; exact ⟨h₁, h₂, hr⟩), h₃]

/-- An element at no index of the stride is unchanged. -/
public theorem getElem_mapStride_of_ne (a : Float64Array) (off inc lo hi g) {p : Nat}
    (hp : ∀ i, lo ≤ i → i < hi → p ≠ off + inc * i) (h : p < a.size) :
    (mapStride a off inc lo hi g)[p]'(by simpa using h) = a[p] := by
  simp only [mapStride, getElem_ofFn]
  rw [ite_eq_right]
  intro ⟨h₁, h₂, h₃, h₄⟩
  exact hp _ h₃ h₄ (eq_stride_of_mod h₁ h₂)

public theorem mapStride_of_le (a : Float64Array) (off inc lo hi g) (h : hi ≤ lo) :
    mapStride a off inc lo hi g = a := by
  apply ext_getElem (by simp)
  intro p _ hp
  exact getElem_mapStride_of_ne a off inc lo hi g (fun i h₁ h₂ => by lia) hp

/-- The first step of a stride comes first. -/
theorem mapStride_set (a : Float64Array) (off inc lo hi : Nat) (g : Nat → Float → Float)
    (hlo : lo < hi) (hinc : 0 < inc ∨ hi ≤ 1) (h : off + inc * lo < a.size) :
    mapStride (a.set (off + inc * lo) (g lo a[off + inc * lo]) h) off inc (lo + 1) hi g =
      mapStride a off inc lo hi g := by
  have hinc' : 0 < inc ∨ lo = 0 := by lia
  apply ext_getElem (by simp)
  intro p hp _
  simp only [size_mapStride, size_set] at hp
  by_cases hq : p = off + inc * lo
  · subst hq
    rw [getElem_mapStride_stride a off inc lo hi g ⟨Nat.le_refl _, hlo⟩ hinc' h,
      getElem_mapStride_of_ne _ _ _ _ _ _ _ (by simpa using h)]
    · simp
    · intro i h₁ _ e
      rcases hinc with hinc | hinc
      · have : inc * lo < inc * i := Nat.mul_lt_mul_of_pos_left (by lia) hinc
        lia
      · lia
  · simp only [mapStride, getElem_ofFn, Float64Array.getElem_set]
    rw [ite_eq_right (Ne.symm hq)]
    by_cases hc : off ≤ p ∧ (p - off) % inc = 0
    · have e := eq_stride_of_mod hc.1 hc.2
      have hne : (p - off) / inc ≠ lo := fun h' => hq (by rw [e, h'])
      by_cases hr : (p - off) / inc < hi
      · by_cases hl : lo ≤ (p - off) / inc
        · rw [ite_eq_left ⟨hc.1, hc.2, by lia, hr⟩, ite_eq_left ⟨hc.1, hc.2, hl, hr⟩]
        · rw [ite_eq_right (by lia), ite_eq_right (by lia)]
      · rw [ite_eq_right (by lia), ite_eq_right (by lia)]
    · rw [ite_eq_right (by lia), ite_eq_right (by lia)]

/--
Runs a loop that replaces each element `a[off + inc * j]`, for `j₀ ≤ j < hi`, with
`g j a[off + inc * j]`, and then runs `k`. It is the loop of
`for j in 0...hi do a[off + inc * j] := e`, from step `j₀`, for a term `e` that reads only
`a[off + inc * j]`. The index `off + inc * j` is `OFF + INC * j` as a `Nat`, and the indices are
distinct: `INC > 0`, or the loop has at most one step.
-/
public theorem run_forInFrom_stride {n : Nat} {γ : Type} (hi j₀ : USize)
    (hlo : (0 : USize).toNat ≤ j₀.toNat) (off inc : USize) (OFF INC : Nat)
    (hinc : 0 < INC ∨ hi.toNat ≤ 1)
    (hix : ∀ j : USize, j.toNat < hi.toNat → (off + inc * j).toNat = OFF + INC * j.toNat)
    (g : (j : USize) → j.toNat < hi.toNat → Float → Float) (G : Nat → Float → Float)
    (hg : ∀ j hj v, g j hj v = G j.toNat v)
    (p : ∀ j : USize, j.toNat < hi.toNat → (off + inc * j).toNat < n) (k : Unit → Tail n γ)
    (a : Float64Array) (h : a.size = n) :
    (Tail.forInFrom 0 hi j₀ hlo ()
        (fun j _ hj next _ => Tail.readThen (off + inc * j) (p j hj) fun v =>
          Tail.writeThen (off + inc * j) (p j hj) (g j hj v) (next ())) k).run a h =
      (k ()).run (mapStride a OFF INC j₀.toNat hi.toNat G) (by simp [h]) := by
  obtain ⟨d, hd⟩ : ∃ d, hi.toNat - j₀.toNat = d := ⟨_, rfl⟩
  induction d generalizing j₀ a with
  | zero =>
    have hj : ¬ j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    rw [Tail.forInFrom_eq, dite_eq_right_of_eq_false (eq_false hj)]
    congr 1
    exact (mapStride_of_le a _ _ _ _ G (by lia)).symm
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    have hj' : j₀.toNat < hi.toNat := hj
    rw [Tail.forInFrom_eq, dite_eq_left_of_eq_true (eq_true hj)]
    simp only [Tail.run_readThen, Tail.run_writeThen]
    have hsucc : (j₀ + 1).toNat = j₀.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt]
      have : hi.toNat < USize.size := hi.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      lia
    rw [ih (j₀ + 1) _ _ _ (by rw [hsucc]; lia)]
    congr 1
    have hq := p j₀ hj'
    have e := hix j₀ hj'
    have hq' : OFF + INC * j₀.toNat < a.size := by rw [h, ← e]; exact hq
    rw [hsucc, ← mapStride_set a _ _ _ _ G hj' hinc hq']
    congr 1
    simp only [e]
    congr 1
    exact hg _ _ _

/--
Runs a loop that writes `g j` at each index `off + inc * j`, for `j₀ ≤ j < hi`, and then runs
`k`: the loop of `for j in 0...hi do a[off + inc * j] := e`, for a term `e` that reads no element
of `a`. The index `off + inc * j` is `OFF + INC * j` as a `Nat`, and the indices are distinct.
-/
public theorem run_forInFrom_stride_write {n : Nat} {γ : Type} (hi j₀ : USize)
    (hlo : (0 : USize).toNat ≤ j₀.toNat) (off inc : USize) (OFF INC : Nat)
    (hinc : 0 < INC ∨ hi.toNat ≤ 1)
    (hix : ∀ j : USize, j.toNat < hi.toNat → (off + inc * j).toNat = OFF + INC * j.toNat)
    (g : (j : USize) → j.toNat < hi.toNat → Float) (G : Nat → Float)
    (hg : ∀ j hj, g j hj = G j.toNat)
    (p : ∀ j : USize, j.toNat < hi.toNat → (off + inc * j).toNat < n) (k : Unit → Tail n γ)
    (a : Float64Array) (h : a.size = n) :
    (Tail.forInFrom 0 hi j₀ hlo ()
        (fun j _ hj next _ => Tail.writeThen (off + inc * j) (p j hj) (g j hj) (next ())) k).run a h =
      (k ()).run (mapStride a OFF INC j₀.toNat hi.toNat fun i _ => G i)
        (by simp [h]) := by
  obtain ⟨d, hd⟩ : ∃ d, hi.toNat - j₀.toNat = d := ⟨_, rfl⟩
  induction d generalizing j₀ a with
  | zero =>
    have hj : ¬ j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    rw [Tail.forInFrom_eq, dite_eq_right_of_eq_false (eq_false hj)]
    congr 1
    exact (mapStride_of_le a _ _ _ _ _ (by lia)).symm
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    have hj' : j₀.toNat < hi.toNat := hj
    rw [Tail.forInFrom_eq, dite_eq_left_of_eq_true (eq_true hj)]
    simp only [Tail.run_writeThen]
    have hsucc : (j₀ + 1).toNat = j₀.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt]
      have : hi.toNat < USize.size := hi.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      lia
    rw [ih (j₀ + 1) _ _ _ (by rw [hsucc]; lia)]
    congr 1
    have hq := p j₀ hj'
    have e := hix j₀ hj'
    have hq' : OFF + INC * j₀.toNat < a.size := by rw [h, ← e]; exact hq
    rw [hsucc, ← mapStride_set a _ _ _ _ (fun i _ => G i) hj' hinc hq']
    congr 1
    simp only [e]
    congr 1
    exact hg _ _

/--
A copy of `n` elements from `src` to `dest`, both in bounds unless `n = 0`, is a stride of `1` on
`dest`.
-/
public theorem copySlice_eq_mapStride (src dest : Float64Array) (so d n : Nat)
    (hs : n = 0 ∨ so + n ≤ src.size) (hd : n = 0 ∨ d + n ≤ dest.size) :
    src.copySlice so dest d n = mapStride dest d 1 0 n fun i _ => src[so + i]! := by
  apply ext_getElem (by simp [size_copySlice]; lia)
  intro p h₁ h₂
  rw [getElem_copySlice]
  simp only [mapStride, getElem_ofFn, Nat.mod_one, Nat.div_one]
  by_cases hp : d ≤ p ∧ p - d < n
  · rw [ite_eq_left ⟨hp.1, trivial, Nat.zero_le _, hp.2⟩,
      dite_eq_right (by lia), dite_eq_left (by lia), getElem!_pos src _ (by lia)]
    congr 1
    lia
  · rw [ite_eq_right (by lia)]
    split
    · rfl
    · rw [dite_eq_right (by lia)]

/-- Two strides with the same indices compose: the element `i` is mapped by `g` and then `g'`. -/
public theorem mapStride_mapStride (a : Float64Array) (off inc lo hi : Nat)
    (g g' : Nat → Float → Float) :
    mapStride (mapStride a off inc lo hi g) off inc lo hi g' =
      mapStride a off inc lo hi fun i v => g' i (g i v) := by
  apply ext_getElem (by simp)
  intro p _ _
  simp only [mapStride, getElem_ofFn]
  split <;> rfl

/-- `mapStride` depends only on the values of its function at the steps of the stride. -/
public theorem mapStride_congr (a : Float64Array) (off inc lo hi : Nat) {g g' : Nat → Float → Float}
    (h : ∀ i v, lo ≤ i → i < hi → g i v = g' i v) :
    mapStride a off inc lo hi g = mapStride a off inc lo hi g' := by
  apply ext_getElem (by simp)
  intro p _ _
  simp only [mapStride, getElem_ofFn]
  split
  · rename_i hc; exact h _ _ hc.2.2.1 hc.2.2.2
  · rfl

/--
Steps that each map the same stride, by `G j` at step `j`, map it by the left fold of the `G j`
over `j < n`.
-/
public theorem iterRange_mapStride (a : Float64Array) (off inc lo hi n : Nat)
    (G : Nat → Nat → Float → Float) :
    iterRange (fun j c => mapStride c off inc lo hi (G j)) 0 n a =
      mapStride a off inc lo hi fun i v => Nat.fold n (fun j _ v => G j i v) v := by
  induction n with
  | zero =>
    rw [iterRange_of_le _ (Nat.le_refl _)]
    apply ext_getElem (by simp)
    intro p _ _
    simp only [mapStride, getElem_ofFn, Nat.fold_zero]
    split <;> rfl
  | succ n ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih, mapStride_mapStride]
    simp only [Nat.fold_succ]

/-- A stride over `lo ≤ i < hi` is a stride over a wider range that leaves the other steps. -/
public theorem mapStride_widen (a : Float64Array) (off inc lo hi lo' hi' : Nat)
    (g : Nat → Float → Float) (h₁ : lo' ≤ lo) (h₂ : hi ≤ hi') :
    mapStride a off inc lo hi g =
      mapStride a off inc lo' hi' fun i v => if lo ≤ i ∧ i < hi then g i v else v := by
  apply ext_getElem (by simp)
  intro p _ _
  simp only [mapStride, getElem_ofFn]
  by_cases hc : off ≤ p ∧ (p - off) % inc = 0 ∧ lo ≤ (p - off) / inc ∧ (p - off) / inc < hi
  · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, hc.2.1, by lia, by lia⟩,
      ite_eq_left ⟨hc.2.2.1, hc.2.2.2⟩]
  · rw [ite_eq_right hc]
    split
    · rename_i hc'
      rw [ite_eq_right (fun h => hc ⟨hc'.1, hc'.2.1, h⟩)]
    · rfl

/-- Writing at the step `j` of a stride is a stride over the single step `j`. -/
public theorem set_eq_mapStride (a : Float64Array) (off inc j : Nat) (v : Float)
    (hinc : 0 < inc ∨ j = 0) (h : off + inc * j < a.size) :
    a.set (off + inc * j) v h = mapStride a off inc j (j + 1) fun _ _ => v := by
  obtain ⟨h₁, h₂, h₃⟩ := stride_index (off := off) hinc
  apply ext_getElem (by simp)
  intro p _ _
  simp only [mapStride, getElem_ofFn, Float64Array.getElem_set]
  by_cases hp : off + inc * j = p
  · subst hp
    rw [ite_eq_left rfl, ite_eq_left ⟨h₁, h₂, by lia, by lia⟩]
  · rw [ite_eq_right hp, ite_eq_right]
    intro ⟨h₁', h₂', h₃', h₄'⟩
    exact hp (by rw [eq_stride_of_mod h₁' h₂', show (p - off) / inc = j by lia])

/-- A stride from the step `s` is a stride from the offset of that step. -/
public theorem mapStride_shift (a : Float64Array) (off inc s h : Nat) (g : Nat → Float → Float)
    (hinc : 0 < inc ∨ h = 0) :
    mapStride a (off + inc * s) inc 0 h g = mapStride a off inc s (s + h) fun i v => g (i - s) v := by
  rcases hinc with hinc | rfl
  · apply ext_getElem (by simp)
    intro p _ _
    simp only [mapStride, getElem_ofFn]
    by_cases hp : off + inc * s ≤ p
    · have e₁ : p - off = inc * s + (p - (off + inc * s)) := by lia
      have em : (p - off) % inc = (p - (off + inc * s)) % inc := by
        rw [e₁, Nat.mul_add_mod]
      have ed : (p - off) / inc = s + (p - (off + inc * s)) / inc := by
        rw [e₁, Nat.mul_add_div hinc]
      simp only [em, ed, Nat.add_sub_cancel_left]
      by_cases hc : (p - (off + inc * s)) % inc = 0 ∧ (p - (off + inc * s)) / inc < h
      · rw [ite_eq_left ⟨hp, hc.1, Nat.zero_le _, hc.2⟩,
          ite_eq_left ⟨by lia, hc.1, Nat.le_add_right _ _, Nat.add_lt_add_left hc.2 _⟩]
      · rw [ite_eq_right (by lia), ite_eq_right (by lia)]
    · rw [ite_eq_right (by lia), ite_eq_right]
      intro ⟨h₁, h₂, h₃, _⟩
      have := eq_stride_of_mod h₁ h₂
      have : inc * s ≤ inc * ((p - off) / inc) := Nat.mul_le_mul_left _ h₃
      lia
  · rw [mapStride_of_le _ _ _ _ _ _ (Nat.le_refl _), mapStride_of_le _ _ _ _ _ _ (by lia)]

/-- The identity on a stride leaves the array unchanged. -/
public theorem mapStride_id (a : Float64Array) (off inc lo hi : Nat) :
    mapStride a off inc lo hi (fun _ v => v) = a := by
  apply ext_getElem (by simp)
  intro p _ _
  simp only [mapStride, getElem_ofFn]
  split <;> rfl

/--
Writing `t` at the step `j` of a stride of `n` steps, then updating the steps after `j` by `G` from
the offset of the step `j + 1`, is a stride over the steps `j ≤ i < n`: the triangular update.
-/
public theorem set_mapStride_succ (a : Float64Array) (off inc j n : Nat) (t : Float)
    (G : Nat → Float → Float) (hinc : 0 < inc ∨ n ≤ 1) (hj : j < n) (p : Nat)
    (hp : p = off + inc * j) (h : p < a.size) :
    mapStride (a.set p t h) (off + inc * (j + 1)) inc 0 (n - j - 1) G =
      mapStride a off inc j n fun i v => if i = j then t else G (i - (j + 1)) v := by
  subst hp
  rw [set_eq_mapStride _ _ _ _ _ (by lia), mapStride_shift _ _ _ _ _ _ (by lia),
    show j + 1 + (n - j - 1) = n by lia,
    mapStride_widen _ _ _ j (j + 1) j n _ (Nat.le_refl _) (by lia),
    mapStride_widen _ _ _ (j + 1) n j n _ (by lia) (Nat.le_refl _), mapStride_mapStride]
  apply mapStride_congr
  intro i v h₁ h₂
  by_cases hi : i = j
  · subst hi; simp [show ¬i + 1 ≤ i by lia]
  · have : j + 1 ≤ i := by lia
    simp [hi, this, h₂, show ¬i < j + 1 by lia]

/--
Writing `t` at the step `j` of a stride, then updating the steps before `j` by `G`, is a stride over
the steps `i ≤ j`: the triangular update from the end.
-/
public theorem set_mapStride_pred (a : Float64Array) (off inc j : Nat) (t : Float)
    (G : Nat → Float → Float) (hinc : 0 < inc ∨ j = 0) (p : Nat) (hp : p = off + inc * j)
    (h : p < a.size) :
    mapStride (a.set p t h) off inc 0 j G =
      mapStride a off inc 0 (j + 1) fun i v => if i = j then t else G i v := by
  subst hp
  rw [set_eq_mapStride _ _ _ _ _ hinc,
    mapStride_widen _ _ _ j (j + 1) 0 (j + 1) _ (Nat.zero_le _) (Nat.le_refl _),
    mapStride_widen _ _ _ 0 j 0 (j + 1) _ (Nat.le_refl _) (by lia), mapStride_mapStride]
  apply mapStride_congr
  intro i v _ h₂
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi, show i < j by lia, show ¬j ≤ i by lia]

end BLAS.Float64
