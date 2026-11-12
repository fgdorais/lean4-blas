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
    rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem foldUpTo_loop_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (hf : ∀ i h b, fu i h b = f i.toNat h b)
    (m : USize) (hm : m.toNat = n) (i : USize) (k : Nat) (hk : i.toNat = k) (hkn : k ≤ n)
    (init : β) :
    foldUpTo.loop n fu m hm i (Nat.fold k (fun j hj => f j (by omega)) init) =
      Nat.fold n f init := by
  obtain ⟨d, hd⟩ : ∃ d, n - k = d := ⟨_, rfl⟩
  induction d generalizing i k with
  | zero =>
    rw [foldUpTo.loop, dite_eq_right_of_eq_false (eq_false (by rw [USize.lt_iff_toNat_lt]; omega))]
    obtain rfl : k = n := by omega
    rfl
  | succ d ih =>
    have hi : i.toNat < n := by omega
    have hsucc : (i + 1).toNat = k + 1 := by
      have : m.toNat < USize.size := m.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega), hk]
    rw [foldUpTo.loop, dite_eq_left_of_eq_true (eq_true (by rw [USize.lt_iff_toNat_lt]; omega)),
      hf]
    have := ih (i + 1) (k + 1) hsucc (by omega) (by omega)
    rw [Nat.fold_succ] at this
    subst hk
    exact this

public theorem foldUpTo_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (hf : ∀ i h b, fu i h b = f i.toNat h b)
    (init : β) : foldUpTo n f fu init = Nat.fold n f init := by
  unfold foldUpTo
  split
  · simpa using foldUpTo_loop_eq n f fu hf _ _ 0 0 (by simp) (by omega) init
  · rfl

/-! ## Indices -/

/-- `(x + y).toNat = x.toNat + y.toNat` when the sum doesn't wrap around. -/
public theorem USize.toNat_add_of_lt {x y : USize} (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-- `(x * y).toNat = x.toNat * y.toNat` when the product doesn't wrap around. -/
public theorem USize.toNat_mul_of_lt {x y : USize} (h : x.toNat * y.toNat < USize.size) :
    (x * y).toNat = x.toNat * y.toNat := by
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_mul, Nat.mod_eq_of_lt (by omega)]

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
  rw [iterRange]; simp [show ¬lo < hi by omega]

public theorem size_iterRange (F : Nat → Float64Array → Float64Array)
    (hF : ∀ j a, (F j a).size = a.size) (lo hi : Nat) (a : Float64Array) :
    (iterRange F lo hi a).size = a.size := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le F (by omega)]
  | succ d ih => rw [iterRange_of_lt F (by omega), ih (lo + 1) _ (by omega), hF]

/-- The last step of `iterRange` comes last. -/
public theorem iterRange_succ (F : Nat → Float64Array → Float64Array) {lo hi : Nat} (h : lo ≤ hi)
    (a : Float64Array) : iterRange F lo (hi + 1) a = F hi (iterRange F lo hi a) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    obtain rfl : lo = hi := by omega
    rw [iterRange_of_lt F (by omega), iterRange_of_le F (by omega), iterRange_of_le F (by omega)]
  | succ d ih =>
    rw [iterRange_of_lt F (show lo < hi + 1 by omega), ih (lo := lo + 1) (by omega) _ (by omega),
      ← iterRange_of_lt F (show lo < hi by omega)]

/-- `iterRange` splits at any `mid` between its bounds. -/
public theorem iterRange_split (F : Nat → Float64Array → Float64Array) {lo mid hi : Nat}
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (a : Float64Array) :
    iterRange F lo hi a = iterRange F mid hi (iterRange F lo mid a) := by
  obtain ⟨d, hd⟩ : ∃ d, mid - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    obtain rfl : lo = mid := by omega
    rw [iterRange_of_le F (Nat.le_refl _)]
  | succ d ih =>
    rw [iterRange_of_lt F (show lo < hi by omega), iterRange_of_lt F (show lo < mid by omega),
      ih (by omega) _ (by omega)]

/-- An element that no step changes is unchanged. -/
public theorem getElem!_iterRange_of_frame (F : Nat → Float64Array → Float64Array) (q : Nat)
    {lo hi : Nat} (hF : ∀ j, lo ≤ j → j < hi → ∀ a, (F j a)[q]! = a[q]!) (a : Float64Array) :
    (iterRange F lo hi a)[q]! = a[q]! := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le F (by omega)]
  | succ d ih =>
    rw [iterRange_of_lt F (by omega), ih (fun j h₁ h₂ => hF j (by omega) h₂) _ (by omega),
      hF lo (Nat.le_refl _) (by omega)]

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
    rw [iterRange_succ F (Nat.zero_le _), hg hi (by omega) _ (by rw [size_iterRange F hF, ha]),
      Nat.fold_succ, ih (fun l h => g l (by omega)) (fun l h a => hg l (by omega) a)]

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
    rw [iterRange_of_le _ (by omega)]
    split <;> first | rfl | omega
  | succ d ih =>
    rw [iterRange_of_lt _ (by omega), ih (lo + 1) _ (by simpa using hp) (by omega)]
    by_cases hp' : p = off + lo
    · subst hp'
      have : ¬lo + 1 ≤ lo := by omega
      simp [getElem!_pos, hp, this, show lo < hi by omega]
    · have : (a.set! (off + lo) (G lo a[off + lo]!))[p]! = a[p]! := by
        simp [getElem!_pos, hp, Ne.symm hp']
      rw [this]
      split <;> split <;> first | rfl | omega

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
    rw [iterRange_of_le _ (by omega)]
    split
    · omega
    · split
      · omega
      · rfl
  | succ d ih =>
    rw [iterRange_of_lt _ (by omega), ih (lo + 1) _ (by simpa using hp) (by omega)]
    have e : ∀ q, q < a.size →
        ((a.set! (off + lo) (G lo a[off + lo]!)).set! (off' + lo) (G' lo a[off' + lo]!))[q]! =
          if q = off' + lo then G' lo a[off' + lo]! else if q = off + lo then G lo a[off + lo]!
          else a[q]! := by
      intro q hq
      rw [getElem!_set!_of_lt _ _ _ (by simpa using hq), getElem!_set!_of_lt _ _ _ hq]
      have hne : off' ≠ off := by omega
      by_cases h1 : q = off' + lo
      · simp [h1]
      · by_cases h2 : q = off + lo
        · simp [h2, hne, hne.symm]
        · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    simp only [e p hp]
    by_cases h1 : p = off' + lo
    · subst h1
      simp only [show off' + lo - off' = lo by omega]
      (repeat' split) <;> first | rfl | omega | simp_all
    · by_cases h2 : p = off + lo
      · subst h2
        simp only [show off + lo - off = lo by omega]
        (repeat' split) <;> first | rfl | omega | simp_all
      · (repeat' split) <;> first | rfl | omega

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
    have hj : ¬ j₀ < hi := by rw [USize.lt_iff_toNat_lt]; omega
    rw [Tail.forInFrom_eq, dite_eq_right_of_eq_false (eq_false hj)]
    congr 1
    exact (iterRange_of_le F (by omega) a).symm
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; omega
    have hj' : j₀.toNat < hi.toNat := hj
    rw [Tail.forInFrom_eq, dite_eq_left_of_eq_true (eq_true hj)]
    refine Eq.trans (hbody j₀ hlo hj' _ a h) ?_
    have hsucc : (j₀ + 1).toNat = j₀.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt]
      have : hi.toNat < USize.size := hi.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      omega
    rw [ih (j₀ + 1) _ _ _ (by rw [hsucc]; omega)]
    congr 1
    rw [hsucc, iterRange_of_lt F hj']

end BLAS.Float64
