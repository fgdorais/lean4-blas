/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Level3

/-!
# Blocked `gemm`

`PMat.gemmBlocked` computes `gemm` by blocked loops, about twice as fast, with the same result: each
element of `C` gets the same terms in the same order.

The work is split into small functions: plain recursive loops over the blocks, the columns and the
terms, which call in-place sweeps over the rows. A single in-place program with all the loops
nested would pass every variable of the outer loops through the inner ones, which spills them in
the innermost loop and, past a few levels, keeps the C compiler from turning the calls between the
loops into jumps.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

/-- `(x * y + z).toNat = x.toNat * y.toNat + z.toNat` when it doesn't wrap around. -/
public theorem USize.toNat_mul_add_of_lt {x y z : USize} {X : Nat} (hx : x.toNat = X)
    (h : X * y.toNat + z.toNat < USize.size) : (x * y + z).toNat = X * y.toNat + z.toNat := by
  have hxy : (x * y).toNat = X * y.toNat := by
    rw [USize.toNat_mul_of_lt (by rw [hx]; lia), hx]
  rw [USize.toNat_add_of_lt (by rw [hxy]; lia), hxy]

/--
The window of `len` elements at `x * y + z` fits in an `X × Y` matrix, for `y < Y` and
`z + len ≤ X`.
-/
public theorem toNat_mul_add_add_le {x y z len : USize} {X Y : Nat} (hx : x.toNat = X)
    (hy : y.toNat < Y) (hz : z.toNat + len.toNat ≤ X) (hs : X * Y < USize.size) :
    (x * y + z).toNat + len.toNat ≤ X * Y := by
  have h1 : X * (y.toNat + 1) ≤ X * Y := Nat.mul_le_mul_left _ hy
  rw [Nat.mul_succ] at h1
  rw [USize.toNat_mul_add_of_lt hx (by lia)]
  lia

/-- `(x * y + z).toNat` for an element `z ≤ X` of the column `y < Y` of an `X × Y` matrix. -/
public theorem toNat_mul_add_eq {x y z : USize} {X Y : Nat} (hx : x.toNat = X) (hy : y.toNat < Y)
    (hz : z.toNat ≤ X) (hs : X * Y < USize.size) : (x * y + z).toNat = X * y.toNat + z.toNat :=
  USize.toNat_mul_add_of_lt hx (by
    have h1 : X * (y.toNat + 1) ≤ X * Y := Nat.mul_le_mul_left _ hy
    rw [Nat.mul_succ] at h1; lia)

/-! ## Sweeps over the rows -/

/--
`sweep4 a c cj cj' a₀ a₁ a₂ a₃ len … t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃` adds
`t₀ * a[a₀ + i] + t₁ * a[a₁ + i] + t₂ * a[a₂ + i] + t₃ * a[a₃ + i]`, from the left, to
`c[cj + i]`, and the same with the `s`s to `c[cj' + i]`, for `i < len`. It is the inner loop of
`gemmBlocked`: two columns of `C` and four terms at a time.
-/
public def sweep4 (a c : Float64Array) (cj cj' a₀ a₁ a₂ a₃ len : USize)
    (hc : cj.toNat + len.toNat ≤ c.size) (hc' : cj'.toNat + len.toNat ≤ c.size)
    (h₀ : a₀.toNat + len.toNat ≤ a.size) (h₁ : a₁.toNat + len.toNat ≤ a.size)
    (h₂ : a₂.toNat + len.toNat ≤ a.size) (h₃ : a₃.toNat + len.toNat ≤ a.size)
    (t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃ : Float) : {c' : Float64Array // c'.size = c.size} :=
  inplace c do
    for i in 0...len do
      let x₀ := a.uget (a₀ + i) (InPlaceSyntax.toNat_add_lt_of_window h₀ (by lia))
      let x₁ := a.uget (a₁ + i) (InPlaceSyntax.toNat_add_lt_of_window h₁ (by lia))
      let x₂ := a.uget (a₂ + i) (InPlaceSyntax.toNat_add_lt_of_window h₂ (by lia))
      let x₃ := a.uget (a₃ + i) (InPlaceSyntax.toNat_add_lt_of_window h₃ (by lia))
      c[cj + i] := c[cj + i] + t₀ * x₀ + t₁ * x₁ + t₂ * x₂ + t₃ * x₃
      c[cj' + i] := c[cj' + i] + s₀ * x₀ + s₁ * x₁ + s₂ * x₂ + s₃ * x₃
  then fun _ c' h => ⟨c', h⟩

/-- `sweep4` with one term: adds `t * a[al + i]` to `c[cj + i]` and `s * a[al + i]` to `c[cj' + i]`. -/
public def sweep2 (a c : Float64Array) (cj cj' al len : USize)
    (hc : cj.toNat + len.toNat ≤ c.size) (hc' : cj'.toNat + len.toNat ≤ c.size)
    (ha : al.toNat + len.toNat ≤ a.size) (t s : Float) : {c' : Float64Array // c'.size = c.size} :=
  inplace c do
    for i in 0...len do
      let x := a.uget (al + i) (InPlaceSyntax.toNat_add_lt_of_window ha (by lia))
      c[cj + i] := c[cj + i] + t * x
      c[cj' + i] := c[cj' + i] + s * x
  then fun _ c' h => ⟨c', h⟩

/-- `sweep2` for one column: adds `t * a[al + i]` to `c[cj + i]`, for `i < len`. -/
public def sweep1 (a c : Float64Array) (cj al len : USize)
    (hc : cj.toNat + len.toNat ≤ c.size) (ha : al.toNat + len.toNat ≤ a.size) (t : Float) :
    {c' : Float64Array // c'.size = c.size} :=
  inplace c do
    for i in 0...len do
      c[cj + i] := c[cj + i] +
        t * a.uget (al + i) (InPlaceSyntax.toNat_add_lt_of_window ha (by lia))
  then fun _ c' h => ⟨c', h⟩

theorem getElem!_sweep4 (a c : Float64Array) (cj cj' a₀ a₁ a₂ a₃ len hc hc' h₀ h₁ h₂ h₃)
    (t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃ : Float) (hsmall : c.size < USize.size)
    (hasmall : a.size < USize.size) (hd : cj.toNat + len.toNat ≤ cj'.toNat) (p : Nat)
    (hp : p < c.size) :
    (sweep4 a c cj cj' a₀ a₁ a₂ a₃ len hc hc' h₀ h₁ h₂ h₃ t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃).1[p]! =
      if cj.toNat ≤ p ∧ p < cj.toNat + len.toNat then
        c[p]! + t₀ * a[a₀.toNat + (p - cj.toNat)]! + t₁ * a[a₁.toNat + (p - cj.toNat)]! +
          t₂ * a[a₂.toNat + (p - cj.toNat)]! + t₃ * a[a₃.toNat + (p - cj.toNat)]!
      else if cj'.toNat ≤ p ∧ p < cj'.toNat + len.toNat then
        c[p]! + s₀ * a[a₀.toNat + (p - cj'.toNat)]! + s₁ * a[a₁.toNat + (p - cj'.toNat)]! +
          s₂ * a[a₂.toNat + (p - cj'.toNat)]! + s₃ * a[a₃.toNat + (p - cj'.toNat)]!
      else c[p]! := by
  have hlen : len.toNat < USize.size := len.toNat_lt_size
  unfold sweep4
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun i c =>
      (c.set! (cj.toNat + i) (c[cj.toNat + i]! + t₀ * a[a₀.toNat + i]! + t₁ * a[a₁.toNat + i]! +
          t₂ * a[a₂.toNat + i]! + t₃ * a[a₃.toNat + i]!)).set! (cj'.toNat + i)
        (c[cj'.toNat + i]! + s₀ * a[a₀.toNat + i]! + s₁ * a[a₁.toNat + i]! +
          s₂ * a[a₂.toNat + i]! + s₃ * a[a₃.toNat + i]!)) (hF := by simp)]
  · simp only [Tail.run_done, USize.toNat_zero]
    rw [getElem!_iterRange_set2! cj.toNat cj'.toNat
      (fun i v => v + t₀ * a[a₀.toNat + i]! + t₁ * a[a₁.toNat + i]! + t₂ * a[a₂.toNat + i]! +
        t₃ * a[a₃.toNat + i]!)
      (fun i v => v + s₀ * a[a₀.toNat + i]! + s₁ * a[a₁.toNat + i]! + s₂ * a[a₂.toNat + i]! +
        s₃ * a[a₃.toNat + i]!) 0 len.toNat hd c p hp]
    simp only [Nat.add_zero]
  · intro i _ hi next c₁ h₁'
    simp only [Tail.run_readThen, Tail.run_writeThen]
    apply Tail.run_congr
    have hi' : i.toNat < len.toNat := by simpa using hi
    have e : ∀ {x : USize}, x.toNat + len.toNat ≤ c.size → (x + i).toNat = x.toNat + i.toNat :=
      fun h => USize.toNat_add_of_lt (by lia)
    have ea : ∀ {x : USize}, x.toNat + len.toNat ≤ a.size → (x + i).toNat = x.toNat + i.toNat :=
      fun h => USize.toNat_add_of_lt (by lia)
    simp only [Float64Array.uget_eq_getElem, e hc, e hc', ea h₀, ea h₁, ea h₂, ea h₃,
      Float64Array.set_eq_set!, Float64Array.getElem_eq_getElem!]
    rw [getElem!_set!_of_lt _ _ _ (by lia), ite_eq_right (by lia)]

theorem getElem!_sweep2 (a c : Float64Array) (cj cj' al len hc hc' ha) (t s : Float)
    (hsmall : c.size < USize.size) (hasmall : a.size < USize.size)
    (hd : cj.toNat + len.toNat ≤ cj'.toNat) (p : Nat) (hp : p < c.size) :
    (sweep2 a c cj cj' al len hc hc' ha t s).1[p]! =
      if cj.toNat ≤ p ∧ p < cj.toNat + len.toNat then c[p]! + t * a[al.toNat + (p - cj.toNat)]!
      else if cj'.toNat ≤ p ∧ p < cj'.toNat + len.toNat then
        c[p]! + s * a[al.toNat + (p - cj'.toNat)]!
      else c[p]! := by
  have hlen : len.toNat < USize.size := len.toNat_lt_size
  unfold sweep2
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun i c =>
      (c.set! (cj.toNat + i) (c[cj.toNat + i]! + t * a[al.toNat + i]!)).set! (cj'.toNat + i)
        (c[cj'.toNat + i]! + s * a[al.toNat + i]!)) (hF := by simp)]
  · simp only [Tail.run_done, USize.toNat_zero]
    rw [getElem!_iterRange_set2! cj.toNat cj'.toNat (fun i v => v + t * a[al.toNat + i]!)
      (fun i v => v + s * a[al.toNat + i]!) 0 len.toNat hd c p hp]
    simp only [Nat.add_zero]
  · intro i _ hi next c₁ h₁'
    simp only [Tail.run_readThen, Tail.run_writeThen]
    apply Tail.run_congr
    have hi' : i.toNat < len.toNat := by simpa using hi
    have e : ∀ {x : USize}, x.toNat + len.toNat ≤ c.size → (x + i).toNat = x.toNat + i.toNat :=
      fun h => USize.toNat_add_of_lt (by lia)
    have ea : ∀ {x : USize}, x.toNat + len.toNat ≤ a.size → (x + i).toNat = x.toNat + i.toNat :=
      fun h => USize.toNat_add_of_lt (by lia)
    simp only [Float64Array.uget_eq_getElem, e hc, e hc', ea ha, Float64Array.set_eq_set!,
      Float64Array.getElem_eq_getElem!]
    rw [getElem!_set!_of_lt _ _ _ (by lia), ite_eq_right (by lia)]

theorem getElem!_sweep1 (a c : Float64Array) (cj al len hc ha) (t : Float)
    (hsmall : c.size < USize.size) (hasmall : a.size < USize.size) (p : Nat) (hp : p < c.size) :
    (sweep1 a c cj al len hc ha t).1[p]! =
      if cj.toNat ≤ p ∧ p < cj.toNat + len.toNat then c[p]! + t * a[al.toNat + (p - cj.toNat)]!
      else c[p]! := by
  have hlen : len.toNat < USize.size := len.toNat_lt_size
  unfold sweep1
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun i c =>
      c.set! (cj.toNat + i) (c[cj.toNat + i]! + t * a[al.toNat + i]!)) (hF := by simp)]
  · simp only [Tail.run_done, USize.toNat_zero]
    rw [getElem!_iterRange_set! cj.toNat (fun i v => v + t * a[al.toNat + i]!) 0 len.toNat c p hp]
    simp only [Nat.add_zero]
  · intro i _ hi next c₁ h₁'
    simp only [Tail.run_readThen, Tail.run_writeThen]
    apply Tail.run_congr
    have hi' : i.toNat < len.toNat := by simpa using hi
    have e : ∀ {x : USize}, x.toNat + len.toNat ≤ c.size → (x + i).toNat = x.toNat + i.toNat :=
      fun h => USize.toNat_add_of_lt (by lia)
    have ea : ∀ {x : USize}, x.toNat + len.toNat ≤ a.size → (x + i).toNat = x.toNat + i.toNat :=
      fun h => USize.toNat_add_of_lt (by lia)
    simp only [Float64Array.uget_eq_getElem, e hc, ea ha, Float64Array.set_eq_set!,
      Float64Array.getElem_eq_getElem!]

/-! ## The loops -/

/-- The conditions under which `gemmBlocked` runs its loops: every index fits in a `USize`. -/
@[expose] public def gemmFits (m n k : Nat) : Prop :=
  m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
    m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
    (k + 128) * (m + 256) < USize.size

public instance : Decidable (gemmFits m n k) := by unfold gemmFits; infer_instance

namespace PMat

variable {m n k : Nat}

/--
Adds the terms `l ≤ l' < l₁` to the rows `i₀ ≤ i < i₀ + len` of the columns `j` and `j + 1` of
`C`, in the array `c`: four terms at a time by `sweep4`, then one at a time by `sweep2`.
-/
public def gemmPairTerms (α : Float) (A : PMat m k) (B : PMat k n) (hs : gemmFits m n k)
    (j : USize) (hj : j.toNat + 1 < n) (i₀ len : USize) (hw : i₀.toNat + len.toNat ≤ m)
    (l l₁ : USize) (hl : l.toNat ≤ l₁.toNat) (hl₁ : l₁.toNat ≤ k)
    (c : Float64Array) (hc : c.size = m * n) : {c' : Float64Array // c'.size = m * n} :=
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
  have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
  have hj1 : (j + 1).toNat = j.toNat + 1 := by
    rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]
  have hsub : (l₁ - l).toNat = l₁.toNat - l.toNat :=
    USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia)
  have hcj : (m.toUSize * j + i₀).toNat + len.toNat ≤ c.size := by
    rw [hc]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.1
  have hcj' : (m.toUSize * (j + 1) + i₀).toNat + len.toNat ≤ c.size := by
    rw [hc]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.1
  have hbj : (k.toUSize * j).toNat + k.toUSize.toNat ≤ B.data.size := by
    rw [B.size_data]
    exact toNat_mul_add_le (n := n) (by lia) (by rw [hku]; exact Nat.le_refl _) hs'.2.2.1
  have hbj' : (k.toUSize * (j + 1)).toNat + k.toUSize.toNat ≤ B.data.size := by
    rw [B.size_data]
    exact toNat_mul_add_le (n := n) (by lia) (by rw [hku]; exact Nat.le_refl _) hs'.2.2.1
  if h4 : 4 ≤ l₁ - l then
    have h4' : l.toNat + 4 ≤ l₁.toNat := by
      rw [USize.le_iff_toNat_le, hsub] at h4; simp at h4; lia
    let p₁ := l + 1
    have hp₁ : p₁.toNat = l.toNat + 1 := by
      rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]
    let p₂ := p₁ + 1
    have hp₂ : p₂.toNat = l.toNat + 2 := by
      rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]; lia
    let p₃ := p₂ + 1
    have hp₃ : p₃.toNat = l.toNat + 3 := by
      rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]; lia
    have hp₄ : (p₃ + 1).toNat = l.toNat + 4 := by
      rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]; lia
    let c' := sweep4 A.data c (m.toUSize * j + i₀) (m.toUSize * (j + 1) + i₀)
      (m.toUSize * l + i₀) (m.toUSize * p₁ + i₀) (m.toUSize * p₂ + i₀) (m.toUSize * p₃ + i₀) len
      hcj hcj'
      (by rw [A.size_data]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.2.1)
      (by rw [A.size_data]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.2.1)
      (by rw [A.size_data]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.2.1)
      (by rw [A.size_data]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.2.1)
      (α * B.data.uget (k.toUSize * j + l)
        (InPlaceSyntax.toNat_add_lt_of_window hbj (by rw [hku]; lia)))
      (α * B.data.uget (k.toUSize * j + p₁)
        (InPlaceSyntax.toNat_add_lt_of_window hbj (by rw [hku]; lia)))
      (α * B.data.uget (k.toUSize * j + p₂)
        (InPlaceSyntax.toNat_add_lt_of_window hbj (by rw [hku]; lia)))
      (α * B.data.uget (k.toUSize * j + p₃)
        (InPlaceSyntax.toNat_add_lt_of_window hbj (by rw [hku]; lia)))
      (α * B.data.uget (k.toUSize * (j + 1) + l)
        (InPlaceSyntax.toNat_add_lt_of_window hbj' (by rw [hku]; lia)))
      (α * B.data.uget (k.toUSize * (j + 1) + p₁)
        (InPlaceSyntax.toNat_add_lt_of_window hbj' (by rw [hku]; lia)))
      (α * B.data.uget (k.toUSize * (j + 1) + p₂)
        (InPlaceSyntax.toNat_add_lt_of_window hbj' (by rw [hku]; lia)))
      (α * B.data.uget (k.toUSize * (j + 1) + p₃)
        (InPlaceSyntax.toNat_add_lt_of_window hbj' (by rw [hku]; lia)))
    gemmPairTerms α A B hs j hj i₀ len hw (p₃ + 1) l₁ (by rw [hp₄]; lia) hl₁ c'.1
      (by rw [c'.2, hc])
  else if h1 : l < l₁ then
    have h1' : l.toNat < l₁.toNat := h1
    have hl1 : (l + 1).toNat = l.toNat + 1 := by
      rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]
    have ha : (m.toUSize * l + i₀).toNat + len.toNat ≤ A.data.size := by
      rw [A.size_data]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.2.1
    let c' := sweep2 A.data c (m.toUSize * j + i₀) (m.toUSize * (j + 1) + i₀)
      (m.toUSize * l + i₀) len hcj hcj' ha
      (α * B.data.uget (k.toUSize * j + l) (InPlaceSyntax.toNat_add_lt_of_window hbj (by rw [hku]; lia)))
      (α * B.data.uget (k.toUSize * (j + 1) + l)
        (InPlaceSyntax.toNat_add_lt_of_window hbj' (by rw [hku]; lia)))
    gemmPairTerms α A B hs j hj i₀ len hw (l + 1) l₁ (by rw [hl1]; lia) hl₁ c'.1
      (by rw [c'.2, hc])
  else ⟨c, hc⟩
termination_by l₁.toNat - l.toNat
decreasing_by
  · change l₁.toNat - (p₃ + 1).toNat < _; lia
  · lia

/-- `gemmPairTerms` for the last column `j`, when `n` is odd, one term at a time by `sweep1`. -/
public def gemmColTerms (α : Float) (A : PMat m k) (B : PMat k n) (hs : gemmFits m n k)
    (j : USize) (hj : j.toNat < n) (i₀ len : USize) (hw : i₀.toNat + len.toNat ≤ m)
    (l l₁ : USize) (_hl : l.toNat ≤ l₁.toNat) (hl₁ : l₁.toNat ≤ k)
    (c : Float64Array) (hc : c.size = m * n) : {c' : Float64Array // c'.size = m * n} :=
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
  have hnu : n.toUSize.toNat = n := by simp [Nat.mod_eq_of_lt (show n < USize.size by lia)]
  have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
  if h1 : l < l₁ then
    have h1' : l.toNat < l₁.toNat := h1
    have hl1 : (l + 1).toNat = l.toNat + 1 := by
      rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]
    have hbj : (k.toUSize * j).toNat + k.toUSize.toNat ≤ B.data.size := by
      rw [B.size_data]
      exact toNat_mul_add_le (n := n) (by lia) (by rw [hku]; exact Nat.le_refl _) hs'.2.2.1
    let c' := sweep1 A.data c (m.toUSize * j + i₀) (m.toUSize * l + i₀) len
      (by rw [hc]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.1)
      (by rw [A.size_data]; exact toNat_mul_add_add_le hmu (by lia) hw hs'.2.1)
      (α * B.data.uget (k.toUSize * j + l)
        (InPlaceSyntax.toNat_add_lt_of_window hbj (by rw [hku]; lia)))
    gemmColTerms α A B hs j hj i₀ len hw (l + 1) l₁ (by rw [hl1]; lia) hl₁ c'.1
      (by rw [c'.2, hc])
  else ⟨c, hc⟩
termination_by l₁.toNat - l.toNat
decreasing_by lia

/--
Adds the terms `l₀ ≤ l < l₁` to the rows `i₀ ≤ i < i₀ + len` of the columns `j ≤ j' < n` of `C`:
two columns at a time by `gemmPairTerms`, then the last one by `gemmColTerms` if there is one.
-/
public def gemmCols (α : Float) (A : PMat m k) (B : PMat k n) (hs : gemmFits m n k)
    (i₀ len : USize) (hw : i₀.toNat + len.toNat ≤ m)
    (l₀ l₁ : USize) (hl : l₀.toNat ≤ l₁.toNat) (hl₁ : l₁.toNat ≤ k)
    (j : USize) (hj : j.toNat ≤ n) (c : Float64Array) (hc : c.size = m * n) :
    {c' : Float64Array // c'.size = m * n} :=
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
  have hnu : n.toUSize.toNat = n := by simp [Nat.mod_eq_of_lt (show n < USize.size by lia)]
  have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
  have hsub : (n.toUSize - j).toNat = n - j.toNat :=
    by rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia), hnu]
  if h2 : 2 ≤ n.toUSize - j then
    have h2' : j.toNat + 2 ≤ n := by
      rw [USize.le_iff_toNat_le, hsub] at h2; simp at h2; lia
    have hj2 : (j + 2).toNat = j.toNat + 2 := by
      rw [USize.toNat_add_of_lt (by simp; lia)]; simp
    let c' := gemmPairTerms α A B hs j (by lia) i₀ len hw l₀ l₁ hl hl₁ c hc
    gemmCols α A B hs i₀ len hw l₀ l₁ hl hl₁ (j + 2) (by rw [hj2]; lia) c'.1 c'.2
  else if h1 : j < n.toUSize then
    gemmColTerms α A B hs j (by have : j.toNat < n.toUSize.toNat := h1; lia) i₀ len hw l₀ l₁
      hl hl₁ c hc
  else ⟨c, hc⟩
termination_by n - j.toNat
decreasing_by lia

/--
Adds the terms `l₀ ≤ l < l₁` to the rows `i₀ ≤ i < m` of `C`, by `gemmCols` on blocks of 256
rows.
-/
public def gemmRowBlocks (α : Float) (A : PMat m k) (B : PMat k n) (hs : gemmFits m n k)
    (l₀ l₁ : USize) (hl : l₀.toNat ≤ l₁.toNat) (hl₁ : l₁.toNat ≤ k)
    (i₀ : USize) (_hi₀ : i₀.toNat < m + 256) (c : Float64Array) (hc : c.size = m * n) :
    {c' : Float64Array // c'.size = m * n} :=
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
  have hnu : n.toUSize.toNat = n := by simp [Nat.mod_eq_of_lt (show n < USize.size by lia)]
  have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
  if h : i₀ < m.toUSize then
    have h' : i₀.toNat < m := by have : i₀.toNat < m.toUSize.toNat := h; lia
    have h256 : (256 : USize).toNat = 256 := by simp
    have hsub : (m.toUSize - i₀).toNat = m - i₀.toNat := by
      rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia), hmu]
    let len := if m.toUSize - i₀ < 256 then m.toUSize - i₀ else 256
    have hlen : len.toNat = min (m - i₀.toNat) 256 := by
      simp only [len]
      split
      · rename_i h
        rw [USize.lt_iff_toNat_lt, hsub, h256] at h
        rw [hsub]; lia
      · rename_i h
        rw [USize.lt_iff_toNat_lt, hsub, h256] at h
        rw [h256]; lia
    have hnext : (i₀ + 256).toNat = i₀.toNat + 256 := by
      rw [USize.toNat_add_of_lt (by rw [h256]; lia), h256]
    let c' := gemmCols α A B hs i₀ len (by lia) l₀ l₁ hl hl₁ 0 (by simp) c hc
    gemmRowBlocks α A B hs l₀ l₁ hl hl₁ (i₀ + 256) (by lia) c'.1 c'.2
  else ⟨c, hc⟩
termination_by m + 256 - i₀.toNat
decreasing_by lia

/-- Adds the terms `l₀ ≤ l < k` to `C`, by `gemmRowBlocks` on blocks of 128 terms. -/
public def gemmTermBlocks (α : Float) (A : PMat m k) (B : PMat k n) (hs : gemmFits m n k)
    (l₀ : USize) (_hl₀ : l₀.toNat ≤ k) (c : Float64Array) (hc : c.size = m * n) :
    {c' : Float64Array // c'.size = m * n} :=
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
  have hnu : n.toUSize.toNat = n := by simp [Nat.mod_eq_of_lt (show n < USize.size by lia)]
  have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
  if h : l₀ < k.toUSize then
    have h' : l₀.toNat < k := by have : l₀.toNat < k.toUSize.toNat := h; lia
    have h128 : (128 : USize).toNat = 128 := by simp
    have hsub : (k.toUSize - l₀).toNat = k - l₀.toNat := by
      rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia), hku]
    let l₁ := if k.toUSize - l₀ < 128 then k.toUSize else l₀ + 128
    have hl₁ : l₁.toNat = min k (l₀.toNat + 128) := by
      simp only [l₁]
      split
      · rename_i h
        rw [USize.lt_iff_toNat_lt, hsub, h128] at h
        rw [hku]; lia
      · rename_i h
        rw [USize.lt_iff_toNat_lt, hsub, h128] at h
        rw [USize.toNat_add_of_lt (by rw [h128]; lia), h128]; lia
    let c' := gemmRowBlocks α A B hs l₀ l₁ (by lia) (by lia) 0 (by simp) c hc
    gemmTermBlocks α A B hs l₁ (by lia) c'.1 c'.2
  else ⟨c, hc⟩
termination_by k + 1 - l₀.toNat
decreasing_by change k + 1 - l₁.toNat < _; lia

/--
`gemmBlocked α A B β C` is `gemm α A B β C`, by blocked loops that are about twice as fast. It
scales `C` by `β`, then, for each block of 128 terms `l` and each block of 256 rows of `C`, it
sweeps the rows of the block for two columns of `C` and four terms at a time: each sweep reads four
columns of `A` and updates two columns of `C`, and the C compiler vectorizes it. The last column,
when `n` is odd, and the terms that don't make a group of four go one at a time. Each element of
`C` gets the same terms in the same order as in `gemm`, so the result is the same, which
`gemmBlocked_eq` proves.
-/
public def gemmBlocked (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n) :
    PMat m n :=
  if hs : gemmFits m n k then
    have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
        m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
        (k + 128) * (m + 256) < USize.size := hs
    have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
    have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
    have hnu : n.toUSize.toNat = n := by simp [Nat.mod_eq_of_lt (show n < USize.size by lia)]
    have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
    let mu := m.toUSize
    let c := C.data
    have hc : c.size = m * n := C.size_data
    inplace c do
      for j in 0...n.toUSize do
        let cj := mu * j
        have hcj : cj.toNat + mu.toNat ≤ c.size :=
          toNat_mul_add_le (n := n) (by lia) (by rw [hmu, hc]; exact Nat.le_refl _)
            (by rw [hc]; exact hs'.1)
        for i in 0...mu do
          c[cj + i] := β * c[cj + i]
    then fun _ c' h =>
      let c'' := gemmTermBlocks α A B hs 0 (by simp) c' (by rw [h, hc])
      ⟨c''.1, c''.2⟩
  else gemmModel α A B β C

end PMat

end BLAS.Float64

namespace BLAS.Float64.PMat

variable {m n k : Nat}

/-- The element `(i, j)` of `gemm α A B β C` after its first `L` terms. -/
def gemmPartial (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (i j L : Nat) : Float :=
  Nat.fold L (fun l _ s => s + α * B.data[l + k * j]! * A.data[i + m * l]!) (β * C.data[i + m * j]!)

theorem gemmPartial_succ (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (i j L : Nat) : gemmPartial α A B β C i j (L + 1) =
      gemmPartial α A B β C i j L + α * B.data[L + k * j]! * A.data[i + m * L]! := by
  simp [gemmPartial, Nat.fold_succ]

/-- The array `c` holds each element `(i, j)` of `C` after its first `cnt i j` terms. -/
def GemmInv (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (cnt : Nat → Nat → Nat) (c : Float64Array) : Prop :=
  ∀ i j, i < m → j < n → c[i + m * j]! = gemmPartial α A B β C i j (cnt i j)

theorem GemmInv.congr {α : Float} {A : PMat m k} {B : PMat k n} {β : Float} {C : PMat m n}
    {cnt cnt' : Nat → Nat → Nat} {c : Float64Array} (h : GemmInv α A B β C cnt c)
    (e : ∀ i j, i < m → j < n → cnt i j = cnt' i j) : GemmInv α A B β C cnt' c := by
  intro i j hi hj; rw [h i j hi hj, e i j hi hj]

/-- The element `r + m * j'` is in the window of `len` rows at `i₀` in column `j`. -/
theorem window_iff {m j j' r i₀ len : Nat} (hr : r < m) (hw : i₀ + len ≤ m) :
    (m * j + i₀ ≤ r + m * j' ∧ r + m * j' < m * j + i₀ + len) ↔
      (j' = j ∧ i₀ ≤ r ∧ r < i₀ + len) := by
  constructor
  · intro ⟨h₁, h₂⟩
    rcases Nat.lt_trichotomy j' j with h | h | h
    · have : m * (j' + 1) ≤ m * j := Nat.mul_le_mul_left m h
      rw [Nat.mul_succ] at this; lia
    · subst h; lia
    · have : m * (j + 1) ≤ m * j' := Nat.mul_le_mul_left m h
      rw [Nat.mul_succ] at this; lia
  · rintro ⟨rfl, h₁, h₂⟩; lia

theorem GemmInv.sweep4 {α : Float} {A : PMat m k} {B : PMat k n} {β : Float} {C : PMat m n}
    {cnt : Nat → Nat → Nat} {c : Float64Array} (hinv : GemmInv α A B β C cnt c)
    (hc : c.size = m * n) (hsmall : m * n < USize.size) (hasmall : m * k < USize.size)
    {j i₀ len L : Nat} (hj : j + 1 < n) (hw : i₀ + len ≤ m) (_hL : L + 4 ≤ k)
    (hcnt : ∀ r, i₀ ≤ r → r < i₀ + len → cnt r j = L ∧ cnt r (j + 1) = L)
    (cj cj' a₀ a₁ a₂ a₃ lenu : USize) (hcjN : cj.toNat = m * j + i₀)
    (hcj'N : cj'.toNat = m * (j + 1) + i₀) (hlen : lenu.toNat = len)
    (ha₀ : a₀.toNat = m * L + i₀) (ha₁ : a₁.toNat = m * (L + 1) + i₀)
    (ha₂ : a₂.toNat = m * (L + 2) + i₀) (ha₃ : a₃.toNat = m * (L + 3) + i₀)
    (hc₁ hc₂ h₀ h₁ h₂ h₃)
    (t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃ : Float)
    (ht₀ : t₀ = α * B.data[L + k * j]!) (ht₁ : t₁ = α * B.data[(L + 1) + k * j]!)
    (ht₂ : t₂ = α * B.data[(L + 2) + k * j]!) (ht₃ : t₃ = α * B.data[(L + 3) + k * j]!)
    (hs₀ : s₀ = α * B.data[L + k * (j + 1)]!) (hs₁ : s₁ = α * B.data[(L + 1) + k * (j + 1)]!)
    (hs₂ : s₂ = α * B.data[(L + 2) + k * (j + 1)]!)
    (hs₃ : s₃ = α * B.data[(L + 3) + k * (j + 1)]!) :
    GemmInv α A B β C (fun r j' => if i₀ ≤ r ∧ r < i₀ + len ∧ (j' = j ∨ j' = j + 1) then L + 4
        else cnt r j')
      (sweep4 A.data c cj cj' a₀ a₁ a₂ a₃ lenu hc₁ hc₂ h₀ h₁ h₂ h₃ t₀ t₁ t₂ t₃ s₀ s₁ s₂ s₃).1 := by
  intro r j' hr hj'
  have hp := index_lt hr hj'
  have hcs : c.size < USize.size := by lia
  have has : A.data.size < USize.size := by rw [A.size_data]; exact hasmall
  have hd : cj.toNat + lenu.toNat ≤ cj'.toNat := by rw [hcjN, hcj'N, hlen, Nat.mul_succ]; lia
  rw [getElem!_sweep4 (hsmall := hcs) (hasmall := has) (hd := hd) (hp := by lia)]
  simp only [hcjN, hcj'N, hlen, ha₀, ha₁, ha₂, ha₃]
  have w₀ := window_iff (j := j) (j' := j') hr hw
  have w₁ := window_iff (j := j + 1) (j' := j') hr hw
  by_cases h₀ : j' = j ∧ i₀ ≤ r ∧ r < i₀ + len
  · obtain ⟨rfl, hr₁, hr₂⟩ := h₀
    rw [ite_eq_left (w₀.2 ⟨rfl, hr₁, hr₂⟩), ite_eq_left ⟨hr₁, hr₂, Or.inl rfl⟩, hinv r j' hr hj',
      (hcnt r hr₁ hr₂).1]
    simp only [gemmPartial_succ, ht₀, ht₁, ht₂, ht₃]
    rw [show m * L + i₀ + (r + m * j' - (m * j' + i₀)) = r + m * L by lia,
      show m * (L + 1) + i₀ + (r + m * j' - (m * j' + i₀)) = r + m * (L + 1) by lia,
      show m * (L + 2) + i₀ + (r + m * j' - (m * j' + i₀)) = r + m * (L + 2) by lia,
      show m * (L + 3) + i₀ + (r + m * j' - (m * j' + i₀)) = r + m * (L + 3) by lia]
  · rw [ite_eq_right (fun h => h₀ (w₀.1 h))]
    by_cases h₁ : j' = j + 1 ∧ i₀ ≤ r ∧ r < i₀ + len
    · obtain ⟨rfl, hr₁, hr₂⟩ := h₁
      rw [ite_eq_left (w₁.2 ⟨rfl, hr₁, hr₂⟩), ite_eq_left ⟨hr₁, hr₂, Or.inr rfl⟩, hinv r _ hr hj',
        (hcnt r hr₁ hr₂).2]
      simp only [gemmPartial_succ, hs₀, hs₁, hs₂, hs₃]
      rw [show m * L + i₀ + (r + m * (j + 1) - (m * (j + 1) + i₀)) = r + m * L by lia,
        show m * (L + 1) + i₀ + (r + m * (j + 1) - (m * (j + 1) + i₀)) = r + m * (L + 1) by lia,
        show m * (L + 2) + i₀ + (r + m * (j + 1) - (m * (j + 1) + i₀)) = r + m * (L + 2) by lia,
        show m * (L + 3) + i₀ + (r + m * (j + 1) - (m * (j + 1) + i₀)) = r + m * (L + 3) by lia]
    · rw [ite_eq_right (fun h => h₁ (w₁.1 h)), hinv r j' hr hj', ite_eq_right]
      intro ⟨hr₁, hr₂, h⟩
      rcases h with h | h
      · exact h₀ ⟨h, hr₁, hr₂⟩
      · exact h₁ ⟨h, hr₁, hr₂⟩

theorem GemmInv.sweep2 {α : Float} {A : PMat m k} {B : PMat k n} {β : Float} {C : PMat m n}
    {cnt : Nat → Nat → Nat} {c : Float64Array} (hinv : GemmInv α A B β C cnt c)
    (hc : c.size = m * n) (hsmall : m * n < USize.size) (hasmall : m * k < USize.size)
    {j i₀ len L : Nat} (hj : j + 1 < n) (hw : i₀ + len ≤ m) (_hL : L < k)
    (hcnt : ∀ r, i₀ ≤ r → r < i₀ + len → cnt r j = L ∧ cnt r (j + 1) = L)
    (cj cj' al lenu : USize) (hcjN : cj.toNat = m * j + i₀)
    (hcj'N : cj'.toNat = m * (j + 1) + i₀) (hlen : lenu.toNat = len)
    (haN : al.toNat = m * L + i₀) (hc₁ hc₂ ha) (t s : Float)
    (ht : t = α * B.data[L + k * j]!) (hs : s = α * B.data[L + k * (j + 1)]!) :
    GemmInv α A B β C (fun r j' => if i₀ ≤ r ∧ r < i₀ + len ∧ (j' = j ∨ j' = j + 1) then L + 1
        else cnt r j')
      (sweep2 A.data c cj cj' al lenu hc₁ hc₂ ha t s).1 := by
  intro r j' hr hj'
  have hp := index_lt hr hj'
  have hcs : c.size < USize.size := by lia
  have has : A.data.size < USize.size := by rw [A.size_data]; exact hasmall
  have hd : cj.toNat + lenu.toNat ≤ cj'.toNat := by rw [hcjN, hcj'N, hlen, Nat.mul_succ]; lia
  rw [getElem!_sweep2 (hsmall := hcs) (hasmall := has) (hd := hd) (hp := by lia)]
  simp only [hcjN, hcj'N, hlen, haN]
  have w₀ := window_iff (j := j) (j' := j') hr hw
  have w₁ := window_iff (j := j + 1) (j' := j') hr hw
  by_cases h₀ : j' = j ∧ i₀ ≤ r ∧ r < i₀ + len
  · obtain ⟨rfl, hr₁, hr₂⟩ := h₀
    rw [ite_eq_left (w₀.2 ⟨rfl, hr₁, hr₂⟩), ite_eq_left ⟨hr₁, hr₂, Or.inl rfl⟩, hinv r j' hr hj',
      (hcnt r hr₁ hr₂).1, gemmPartial_succ, ht,
      show m * L + i₀ + (r + m * j' - (m * j' + i₀)) = r + m * L by lia]
  · rw [ite_eq_right (fun h => h₀ (w₀.1 h))]
    by_cases h₁ : j' = j + 1 ∧ i₀ ≤ r ∧ r < i₀ + len
    · obtain ⟨rfl, hr₁, hr₂⟩ := h₁
      rw [ite_eq_left (w₁.2 ⟨rfl, hr₁, hr₂⟩), ite_eq_left ⟨hr₁, hr₂, Or.inr rfl⟩, hinv r _ hr hj',
        (hcnt r hr₁ hr₂).2, gemmPartial_succ, hs,
        show m * L + i₀ + (r + m * (j + 1) - (m * (j + 1) + i₀)) = r + m * L by lia]
    · rw [ite_eq_right (fun h => h₁ (w₁.1 h)), hinv r j' hr hj', ite_eq_right]
      intro ⟨hr₁, hr₂, h⟩
      rcases h with h | h
      · exact h₀ ⟨h, hr₁, hr₂⟩
      · exact h₁ ⟨h, hr₁, hr₂⟩

theorem GemmInv.sweep1 {α : Float} {A : PMat m k} {B : PMat k n} {β : Float} {C : PMat m n}
    {cnt : Nat → Nat → Nat} {c : Float64Array} (hinv : GemmInv α A B β C cnt c)
    (hc : c.size = m * n) (hsmall : m * n < USize.size) (hasmall : m * k < USize.size)
    {j i₀ len L : Nat} (hj : j < n) (hw : i₀ + len ≤ m) (_hL : L < k)
    (hcnt : ∀ r, i₀ ≤ r → r < i₀ + len → cnt r j = L)
    (cj al lenu : USize) (hcjN : cj.toNat = m * j + i₀) (hlen : lenu.toNat = len)
    (haN : al.toNat = m * L + i₀) (hc₁ ha) (t : Float) (ht : t = α * B.data[L + k * j]!) :
    GemmInv α A B β C (fun r j' => if i₀ ≤ r ∧ r < i₀ + len ∧ j' = j then L + 1 else cnt r j')
      (sweep1 A.data c cj al lenu hc₁ ha t).1 := by
  intro r j' hr hj'
  have hp := index_lt hr hj'
  have hcs : c.size < USize.size := by lia
  have has : A.data.size < USize.size := by rw [A.size_data]; exact hasmall
  rw [getElem!_sweep1 (hsmall := hcs) (hasmall := has) (hp := by lia)]
  simp only [hcjN, hlen, haN]
  have w₀ := window_iff (j := j) (j' := j') hr hw
  by_cases h₀ : j' = j ∧ i₀ ≤ r ∧ r < i₀ + len
  · obtain ⟨rfl, hr₁, hr₂⟩ := h₀
    rw [ite_eq_left (w₀.2 ⟨rfl, hr₁, hr₂⟩), ite_eq_left ⟨hr₁, hr₂, rfl⟩, hinv r j' hr hj',
      hcnt r hr₁ hr₂, gemmPartial_succ, ht,
      show m * L + i₀ + (r + m * j' - (m * j' + i₀)) = r + m * L by lia]
  · rw [ite_eq_right (fun h => h₀ (w₀.1 h)), hinv r j' hr hj', ite_eq_right]
    intro ⟨hr₁, hr₂, h⟩
    exact h₀ ⟨h, hr₁, hr₂⟩

theorem gemmPairTerms_inv (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (hs : gemmFits m n k) (j : USize) (hj : j.toNat + 1 < n) (i₀ len : USize)
    (hw : i₀.toNat + len.toNat ≤ m) (l l₁ : USize) (hl : l.toNat ≤ l₁.toNat) (hl₁ : l₁.toNat ≤ k)
    (c : Float64Array) (hc : c.size = m * n) (cnt : Nat → Nat → Nat)
    (hinv : GemmInv α A B β C cnt c)
    (hcnt : ∀ r, i₀.toNat ≤ r → r < i₀.toNat + len.toNat →
      cnt r j.toNat = l.toNat ∧ cnt r (j.toNat + 1) = l.toNat) :
    GemmInv α A B β C (fun r j' => if i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧
        (j' = j.toNat ∨ j' = j.toNat + 1) then l₁.toNat else cnt r j')
      (gemmPairTerms α A B hs j hj i₀ len hw l l₁ hl hl₁ c hc).1 := by
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
  have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
  have hj1 : (j + 1).toNat = j.toNat + 1 := by
    rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]
  have hcjN : (m.toUSize * j + i₀).toNat = m * j.toNat + i₀.toNat :=
    toNat_mul_add_eq hmu (show j.toNat < n by lia) (by lia) hs'.1
  have hcj'N : (m.toUSize * (j + 1) + i₀).toNat = m * (j.toNat + 1) + i₀.toNat := by
    rw [toNat_mul_add_eq hmu (show (j + 1).toNat < n by lia) (by lia) hs'.1, hj1]
  have hA : ∀ x : USize, x.toNat < k →
      (m.toUSize * x + i₀).toNat = m * x.toNat + i₀.toNat :=
    fun x hx => toNat_mul_add_eq hmu hx (by lia) hs'.2.1
  have hB : ∀ (jj ll : USize) (h), jj.toNat < n → ll.toNat ≤ k →
      α * B.data.uget (k.toUSize * jj + ll) h = α * B.data[ll.toNat + k * jj.toNat]! :=
    fun jj ll h hjj hll => by
      rw [Float64Array.uget_eq_getElem, Float64Array.getElem_eq_getElem!,
        toNat_mul_add_eq hku hjj hll hs'.2.2.1, Nat.add_comm]
  obtain ⟨d, hd⟩ : ∃ d, l₁.toNat - l.toNat = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing l c cnt with
  | _ d ih =>
  rw [gemmPairTerms]
  split
  · rename_i h4
    have h4' : l.toNat + 4 ≤ l₁.toNat := by
      rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia)]
        at h4
      simp at h4; lia
    have e1 : ∀ x : USize, x.toNat + 1 ≤ k → (x + 1).toNat = x.toNat + 1 := fun x hx => by
      rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]
    have hp₁ : (l + 1).toNat = l.toNat + 1 := e1 _ (by lia)
    have hp₂ : (l + 1 + 1).toNat = l.toNat + 2 := by rw [e1 _ (by lia), hp₁]
    have hp₃ : (l + 1 + 1 + 1).toNat = l.toNat + 3 := by rw [e1 _ (by lia), hp₂]
    have hp₄ : (l + 1 + 1 + 1 + 1).toNat = l.toNat + 4 := by rw [e1 _ (by lia), hp₃]
    dsimp only
    refine GemmInv.congr (ih (l₁.toNat - (l.toNat + 4)) (by lia) (l + 1 + 1 + 1 + 1) _ _ _
      (fun r j' => if i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ (j' = j.toNat ∨ j' = j.toNat + 1)
        then l.toNat + 4 else cnt r j') ?inv ?cnt ?hd) ?e
    case hd => rw [hp₄]
    case cnt =>
      intro r h₁ h₂
      simp only [h₁, h₂, true_or, or_true, ite_true, hp₄, and_self]
    case inv =>
      apply GemmInv.sweep4 hinv hc hs'.1 hs'.2.1 (j := j.toNat) (by lia) hw (by lia) hcnt
      · exact hcjN
      · exact hcj'N
      · rfl
      · exact hA _ (by lia)
      · rw [hA _ (by lia), hp₁]
      · rw [hA _ (by lia), hp₂]
      · rw [hA _ (by lia), hp₃]
      · rw [hB _ _ _ (by lia) (by lia)]
      · rw [hB _ _ _ (by lia) (by lia), hp₁]
      · rw [hB _ _ _ (by lia) (by lia), hp₂]
      · rw [hB _ _ _ (by lia) (by lia), hp₃]
      · rw [hB _ _ _ (by lia) (by lia), hj1]
      · rw [hB _ _ _ (by lia) (by lia), hp₁, hj1]
      · rw [hB _ _ _ (by lia) (by lia), hp₂, hj1]
      · rw [hB _ _ _ (by lia) (by lia), hp₃, hj1]
    intro r j' _ _
    by_cases hW : i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ (j' = j.toNat ∨ j' = j.toNat + 1)
    · simp [hW]
    · simp [hW]
  · split
    · rename_i h1
      have h1' : l.toNat < l₁.toNat := h1
      have hl1 : (l + 1).toNat = l.toNat + 1 := by
        rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]
      dsimp only
      refine GemmInv.congr (ih (l₁.toNat - (l.toNat + 1)) (by lia) (l + 1) _ _ _
        (fun r j' => if i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧
          (j' = j.toNat ∨ j' = j.toNat + 1) then l.toNat + 1 else cnt r j') ?inv2 ?cnt2 ?hd2) ?e2
      case hd2 => rw [hl1]
      case cnt2 =>
        intro r h₁ h₂
        simp only [h₁, h₂, true_or, or_true, ite_true, hl1, and_self]
      case inv2 =>
        apply GemmInv.sweep2 hinv hc hs'.1 hs'.2.1 (j := j.toNat) (by lia) hw (by lia) hcnt
        · exact hcjN
        · exact hcj'N
        · rfl
        · exact hA _ (by lia)
        · rw [hB _ _ _ (by lia) (by lia)]
        · rw [hB _ _ _ (by lia) (by lia), hj1]
      intro r j' _ _
      by_cases hW : i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ (j' = j.toNat ∨ j' = j.toNat + 1)
      · simp [hW]
      · simp [hW]
    · rename_i h4 h1
      have hll : l₁.toNat = l.toNat := by
        have : ¬ l.toNat < l₁.toNat := h1
        lia
      refine GemmInv.congr hinv ?_
      intro r j' _ _
      by_cases hW : i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ (j' = j.toNat ∨ j' = j.toNat + 1)
      · rw [ite_eq_left hW, hll]
        rcases hW.2.2 with rfl | rfl
        · exact (hcnt r hW.1 hW.2.1).1
        · exact (hcnt r hW.1 hW.2.1).2
      · rw [ite_eq_right hW]

theorem gemmColTerms_inv (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (hs : gemmFits m n k) (j : USize) (hj : j.toNat < n) (i₀ len : USize)
    (hw : i₀.toNat + len.toNat ≤ m) (l l₁ : USize) (hl : l.toNat ≤ l₁.toNat) (hl₁ : l₁.toNat ≤ k)
    (c : Float64Array) (hc : c.size = m * n) (cnt : Nat → Nat → Nat)
    (hinv : GemmInv α A B β C cnt c)
    (hcnt : ∀ r, i₀.toNat ≤ r → r < i₀.toNat + len.toNat → cnt r j.toNat = l.toNat) :
    GemmInv α A B β C (fun r j' => if i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ j' = j.toNat
        then l₁.toNat else cnt r j')
      (gemmColTerms α A B hs j hj i₀ len hw l l₁ hl hl₁ c hc).1 := by
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
  have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
  have hcjN : (m.toUSize * j + i₀).toNat = m * j.toNat + i₀.toNat :=
    toNat_mul_add_eq hmu hj (by lia) hs'.1
  have hA : ∀ x : USize, x.toNat < k →
      (m.toUSize * x + i₀).toNat = m * x.toNat + i₀.toNat :=
    fun x hx => toNat_mul_add_eq hmu hx (by lia) hs'.2.1
  have hB : ∀ (jj ll : USize) (h), jj.toNat < n → ll.toNat ≤ k →
      α * B.data.uget (k.toUSize * jj + ll) h = α * B.data[ll.toNat + k * jj.toNat]! :=
    fun jj ll h hjj hll => by
      rw [Float64Array.uget_eq_getElem, Float64Array.getElem_eq_getElem!,
        toNat_mul_add_eq hku hjj hll hs'.2.2.1, Nat.add_comm]
  obtain ⟨d, hd⟩ : ∃ d, l₁.toNat - l.toNat = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing l c cnt with
  | _ d ih =>
  rw [gemmColTerms]
  split
  · rename_i h1
    have h1' : l.toNat < l₁.toNat := h1
    have hl1 : (l + 1).toNat = l.toNat + 1 := by
      rw [USize.toNat_add_of_lt (by simp only [USize.toNat_one]; lia), USize.toNat_one]
    dsimp only
    refine GemmInv.congr (ih (l₁.toNat - (l.toNat + 1)) (by lia) (l + 1) _ _ _
      (fun r j' => if i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ j' = j.toNat
        then l.toNat + 1 else cnt r j') ?inv ?cnt ?hd) ?e
    case hd => rw [hl1]
    case cnt =>
      intro r h₁ h₂
      simp only [h₁, h₂, ite_true, hl1, and_self]
    case inv =>
      apply GemmInv.sweep1 hinv hc hs'.1 hs'.2.1 (j := j.toNat) hj hw (by lia) hcnt
      · exact hcjN
      · rfl
      · exact hA _ (by lia)
      · rw [hB _ _ _ (by lia) (by lia)]
    intro r j' _ _
    by_cases hW : i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ j' = j.toNat
    · simp [hW]
    · simp [hW]
  · rename_i h1
    have hll : l₁.toNat = l.toNat := by
      have : ¬ l.toNat < l₁.toNat := h1
      lia
    refine GemmInv.congr hinv ?_
    intro r j' _ _
    by_cases hW : i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ j' = j.toNat
    · rw [ite_eq_left hW, hll, hW.2.2]
      exact hcnt r hW.1 hW.2.1
    · rw [ite_eq_right hW]

theorem gemmCols_inv (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (hs : gemmFits m n k) (i₀ len : USize) (hw : i₀.toNat + len.toNat ≤ m)
    (l₀ l₁ : USize) (hl : l₀.toNat ≤ l₁.toNat) (hl₁ : l₁.toNat ≤ k)
    (j : USize) (hj : j.toNat ≤ n) (c : Float64Array) (hc : c.size = m * n)
    (cnt : Nat → Nat → Nat) (hinv : GemmInv α A B β C cnt c)
    (hcnt : ∀ r j', i₀.toNat ≤ r → r < i₀.toNat + len.toNat → j.toNat ≤ j' → j' < n →
      cnt r j' = l₀.toNat) :
    GemmInv α A B β C (fun r j' => if i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ j.toNat ≤ j'
        then l₁.toNat else cnt r j')
      (gemmCols α A B hs i₀ len hw l₀ l₁ hl hl₁ j hj c hc).1 := by
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hnu : n.toUSize.toNat = n := by simp [Nat.mod_eq_of_lt (show n < USize.size by lia)]
  obtain ⟨d, hd⟩ : ∃ d, n - j.toNat = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing j c cnt with
  | _ d ih =>
  have hsub : (n.toUSize - j).toNat = n - j.toNat :=
    by rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia), hnu]
  rw [gemmCols]
  split
  · rename_i h2
    have h2' : j.toNat + 2 ≤ n := by
      rw [USize.le_iff_toNat_le, hsub] at h2; simp at h2; lia
    have hj2 : (j + 2).toNat = j.toNat + 2 := by
      rw [USize.toNat_add_of_lt (by simp; lia)]; simp
    dsimp only
    have h₁ := gemmPairTerms_inv α A B β C hs j (by lia) i₀ len hw l₀ l₁ hl hl₁ c hc cnt hinv
      (fun r hr₁ hr₂ => ⟨hcnt r _ hr₁ hr₂ (Nat.le_refl _) (by lia),
        hcnt r _ hr₁ hr₂ (by lia) (by lia)⟩)
    refine GemmInv.congr (ih (n - (j.toNat + 2)) (by lia) (j + 2) (by lia) _ _ _ h₁ ?_
      (by rw [hj2])) ?_
    · intro r j' hr₁ hr₂ hj₁ hj₂
      rw [hj2] at hj₁
      rw [ite_eq_right (by lia)]
      exact hcnt r j' hr₁ hr₂ (by lia) hj₂
    · intro r j' _ _
      rw [hj2]
      by_cases hW : i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat
      · by_cases hj₃ : j.toNat ≤ j'
        · have : j.toNat + 2 ≤ j' ∨ j' = j.toNat ∨ j' = j.toNat + 1 := by lia
          rcases this with h | h | h <;> simp [hW, hj₃, h]
        · have : ¬ j.toNat + 2 ≤ j' := by lia
          simp [hW, hj₃, this]; lia
      · have hW' : ∀ P : Prop, ¬ (i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat ∧ P) :=
          fun _ h => hW ⟨h.1, h.2.1⟩
        rw [ite_eq_right (hW' _), ite_eq_right (hW' _), ite_eq_right (hW' _)]
  · split
    · rename_i h2 h1
      have h1' : j.toNat < n := by have : j.toNat < n.toUSize.toNat := h1; lia
      have hlast : j.toNat + 1 = n := by
        rw [USize.le_iff_toNat_le, hsub] at h2; simp at h2; lia
      refine GemmInv.congr (gemmColTerms_inv α A B β C hs j h1' i₀ len hw l₀ l₁ hl hl₁ c hc cnt
        hinv (fun r hr₁ hr₂ => hcnt r _ hr₁ hr₂ (Nat.le_refl _) h1')) ?_
      intro r j' _ hj'
      by_cases hW : i₀.toNat ≤ r ∧ r < i₀.toNat + len.toNat
      · have : j.toNat ≤ j' ↔ j' = j.toNat := by lia
        simp [hW, this]
      · rw [ite_eq_right (fun h => hW ⟨h.1, h.2.1⟩), ite_eq_right (fun h => hW ⟨h.1, h.2.1⟩)]
    · rename_i h2 h1
      have hjn : j.toNat = n := by
        have : ¬ j.toNat < n.toUSize.toNat := h1
        lia
      refine GemmInv.congr hinv ?_
      intro r j' _ hj'
      have : ¬ j.toNat ≤ j' := by lia
      simp [this]

theorem gemmRowBlocks_inv (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (hs : gemmFits m n k) (l₀ l₁ : USize) (hl : l₀.toNat ≤ l₁.toNat) (hl₁ : l₁.toNat ≤ k)
    (i₀ : USize) (hi₀ : i₀.toNat < m + 256) (c : Float64Array) (hc : c.size = m * n)
    (cnt : Nat → Nat → Nat) (hinv : GemmInv α A B β C cnt c)
    (hcnt : ∀ r j', i₀.toNat ≤ r → r < m → j' < n → cnt r j' = l₀.toNat) :
    GemmInv α A B β C (fun r j' => if i₀.toNat ≤ r then l₁.toNat else cnt r j')
      (gemmRowBlocks α A B hs l₀ l₁ hl hl₁ i₀ hi₀ c hc).1 := by
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
  have h256 : (256 : USize).toNat = 256 := by simp
  obtain ⟨d, hd⟩ : ∃ d, m + 256 - i₀.toNat = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing i₀ c cnt with
  | _ d ih =>
  rw [gemmRowBlocks]
  split
  · rename_i h
    have h' : i₀.toNat < m := by have : i₀.toNat < m.toUSize.toNat := h; lia
    have hsub : (m.toUSize - i₀).toNat = m - i₀.toNat := by
      rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia), hmu]
    have hnext : (i₀ + 256).toNat = i₀.toNat + 256 := by
      rw [USize.toNat_add_of_lt (by rw [h256]; lia), h256]
    dsimp only
    have hlenN : (if m.toUSize - i₀ < 256 then m.toUSize - i₀ else 256).toNat =
        min (m - i₀.toNat) 256 := by
      split
      · rename_i h
        rw [USize.lt_iff_toNat_lt, hsub, h256] at h
        rw [hsub]; lia
      · rename_i h
        rw [USize.lt_iff_toNat_lt, hsub, h256] at h
        rw [h256]; lia
    have h₁ := gemmCols_inv α A B β C hs i₀
      (if m.toUSize - i₀ < 256 then m.toUSize - i₀ else 256) (by lia) l₀ l₁ hl hl₁ 0
      (by simp) c hc cnt hinv (fun r j' hr₁ hr₂ _ hj' => hcnt r j' hr₁ (by lia) hj')
    refine GemmInv.congr (ih (m + 256 - (i₀.toNat + 256)) (by lia) (i₀ + 256) (by lia) _ _ _
      h₁ ?_ (by rw [hnext])) ?_
    · intro r j' hr₁ hr hj'
      rw [hnext] at hr₁
      rw [ite_eq_right (by lia)]
      exact hcnt r j' (by lia) hr hj'
    · intro r j' hr _
      rw [hnext]
      by_cases h₁ : i₀.toNat + 256 ≤ r
      · rw [ite_eq_left h₁, ite_eq_left (by lia)]
      · rw [ite_eq_right h₁]
        by_cases h₂ : i₀.toNat ≤ r
        · rw [ite_eq_left ⟨h₂, by rw [hlenN]; lia, by simp⟩, ite_eq_left h₂]
        · rw [ite_eq_right (by lia), ite_eq_right h₂]
  · rename_i h
    have h' : m ≤ i₀.toNat := by have : ¬ i₀.toNat < m.toUSize.toNat := h; lia
    refine GemmInv.congr hinv ?_
    intro r j' hr _
    have : ¬ i₀.toNat ≤ r := by lia
    simp [this]

theorem gemmTermBlocks_inv (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n)
    (hs : gemmFits m n k) (l₀ : USize) (hl₀ : l₀.toNat ≤ k) (c : Float64Array)
    (hc : c.size = m * n) (hinv : GemmInv α A B β C (fun _ _ => l₀.toNat) c) :
    GemmInv α A B β C (fun _ _ => k) (gemmTermBlocks α A B hs l₀ hl₀ c hc).1 := by
  have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
      m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
      (k + 128) * (m + 256) < USize.size := hs
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hku : k.toUSize.toNat = k := by simp [Nat.mod_eq_of_lt (show k < USize.size by lia)]
  have h128 : (128 : USize).toNat = 128 := by simp
  obtain ⟨d, hd⟩ : ∃ d, k + 1 - l₀.toNat = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing l₀ c with
  | _ d ih =>
  rw [gemmTermBlocks]
  split
  · rename_i h
    have h' : l₀.toNat < k := by have : l₀.toNat < k.toUSize.toNat := h; lia
    have hsub : (k.toUSize - l₀).toNat = k - l₀.toNat := by
      rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia), hku]
    have hl₁ : (if k.toUSize - l₀ < 128 then k.toUSize else l₀ + 128).toNat =
        min k (l₀.toNat + 128) := by
      split
      · rename_i h
        rw [USize.lt_iff_toNat_lt, hsub, h128] at h
        rw [hku]; lia
      · rename_i h
        rw [USize.lt_iff_toNat_lt, hsub, h128] at h
        rw [USize.toNat_add_of_lt (by rw [h128]; lia), h128]; lia
    dsimp only
    have h₁ := gemmRowBlocks_inv α A B β C hs l₀
      (if k.toUSize - l₀ < 128 then k.toUSize else l₀ + 128) (by lia) (by lia) 0 (by simp)
      c hc _ hinv (fun _ _ _ _ _ => rfl)
    have h₂ : GemmInv α A B β C
        (fun _ _ => (if k.toUSize - l₀ < 128 then k.toUSize else l₀ + 128).toNat) _ :=
      GemmInv.congr h₁ (fun r _ _ _ => by simp)
    exact ih (k + 1 - (if k.toUSize - l₀ < 128 then k.toUSize else l₀ + 128).toNat)
      (by lia) _ (by lia) _ _ h₂ rfl
  · rename_i h
    have h' : k ≤ l₀.toNat := by have : ¬ l₀.toNat < k.toUSize.toNat := h; lia
    exact GemmInv.congr hinv (fun _ _ _ _ => by lia)

/-- The scaling pass of `gemmBlocked`, column by column. -/
def betaPass (m : Nat) (β : Float) (j : Nat) (c : Float64Array) : Float64Array :=
  iterRange (fun i c => c.set! (m * j + i) (β * c[m * j + i]!)) 0 m c

theorem size_betaPass (m β j) (c : Float64Array) : (betaPass m β j c).size = c.size :=
  size_iterRange _ (by simp) _ _ _

theorem getElem!_betaPass (m β j) (c : Float64Array) (q : Nat) (hq : q < c.size) :
    (betaPass m β j c)[q]! = if m * j ≤ q ∧ q < m * j + m then β * c[q]! else c[q]! := by
  have := getElem!_iterRange_set! (m * j) (fun _ x => β * x) 0 m c q hq
  simpa [betaPass] using this

theorem GemmInv.betaPass (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n) :
    GemmInv α A B β C (fun _ _ => 0) (iterRange (PMat.betaPass m β) 0 n C.data) := by
  intro i j hi hj
  have hq := index_lt hi hj
  have hC := C.size_data
  have hsz := size_betaPass m β
  rw [iterRange_split _ (Nat.zero_le _) (show j + 1 ≤ n by lia), getElem!_iterRange_of_frame,
    iterRange_succ _ (Nat.zero_le _), getElem!_betaPass _ _ _ _ _
      (by rw [size_iterRange _ hsz]; lia),
    getElem!_iterRange_of_frame, ite_eq_left (by lia)]
  · simp [gemmPartial]
  · intro j' _ hj' c
    by_cases hc : i + m * j < c.size
    · rw [getElem!_betaPass _ _ _ _ _ hc, ite_eq_right]
      have : m * (j' + 1) ≤ m * j := Nat.mul_le_mul_left _ hj'
      rw [Nat.mul_succ] at this; lia
    · rw [getElem!_neg c _ hc, getElem!_neg _ _ (by rw [hsz]; exact hc)]
  · intro j' hj' _ c
    by_cases hc : i + m * j < c.size
    · rw [getElem!_betaPass _ _ _ _ _ hc, ite_eq_right]
      have : m * (j + 1) ≤ m * j' := Nat.mul_le_mul_left _ hj'
      rw [Nat.mul_succ] at this; lia
    · rw [getElem!_neg c _ hc, getElem!_neg _ _ (by rw [hsz]; exact hc)]

/-- `gemmBlocked` computes `gemm`, with the same result to the bit. -/
public theorem gemmBlocked_eq (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n) :
    gemmBlocked α A B β C = gemmModel α A B β C := by
  unfold gemmBlocked
  split
  · rename_i hs
    have hs' : m * n < USize.size ∧ m * k < USize.size ∧ k * n < USize.size ∧
        m + 256 < USize.size ∧ n + 2 < USize.size ∧ k + 128 < USize.size ∧
        (k + 128) * (m + 256) < USize.size := hs
    have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
    have hmu : m.toUSize.toNat = m := by simp [Nat.mod_eq_of_lt (show m < USize.size by lia)]
    have hnu : n.toUSize.toNat = n := by simp [Nat.mod_eq_of_lt (show n < USize.size by lia)]
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := betaPass m β) (hF := size_betaPass m β)]
    · simp only [Tail.run_done]
      have hinv := gemmTermBlocks_inv α A B β C hs 0 (by simp) _
        (by rw [size_iterRange _ (size_betaPass m β), C.size_data])
        (GemmInv.congr (GemmInv.betaPass α A B β C) (fun _ _ _ _ => by simp))
      apply ext
      intro i j hij
      rw [← gemm_eq, getElem_gemm]
      simp only [gemmEntry, getElem_def, Float64Array.getElem_eq_getElem!, USize.toNat_zero, hnu]
      rw [hinv i j hij.1 hij.2]
      rfl
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_unit (F := fun i c => c.set! (m * j.toNat + i) (β * c[m * j.toNat + i]!))
          (hF := by simp)]
      · simp only [USize.toNat_zero, hmu, betaPass]
      · intro i _ hi next' a' h'
        rw [hmu] at hi
        simp only [Tail.run_readThen, Tail.run_writeThen]
        have h1 : (m.toUSize * j + i).toNat = m * j.toNat + i.toNat :=
          toNat_mul_add_eq hmu hj (by lia) hs'.1
        apply Tail.run_set_eq_set!
        · exact h1
        · have := index_lt hi hj
          have hC := C.size_data
          simp only [h1]
          rw [getElem!_pos a' _ (by rw [h']; rw [Nat.add_comm]; lia)]
  · rfl

@[simp] public theorem getElem_gemmBlocked (α : Float) (A : PMat m k) (B : PMat k n) (β : Float)
    (C : PMat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmBlocked α A B β C)[(i, j)] = gemmEntry α A B β C i j h.1 h.2 := by
  rw [gemmBlocked_eq, ← gemm_eq, getElem_gemm]

public theorem gemmBlocked_eq_gemm (α : Float) (A : PMat m k) (B : PMat k n) (β : Float) (C : PMat m n) :
    gemmBlocked α A B β C = gemm α A B β C := by
  rw [gemmBlocked_eq, gemm_eq]

end BLAS.Float64.PMat
