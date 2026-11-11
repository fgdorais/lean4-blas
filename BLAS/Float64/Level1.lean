/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Vec
public import BLAS.Float64.Loop
public import ScalarArray.InPlaceSyntax

/-!
# Level 1

Vector operations: the updates `axpy`, `scal`, `copy` and `swap`, and the reductions `dot`, `asum`,
`nrm2` and `iamax`.

Each routine has a kernel on `Float64Array`, which runs an in-place loop when the array's size fits
in a `USize`, as it does for every array in memory, and its model otherwise, so that its
specification needs no hypothesis on the size.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Kernel

/-- `α * x + y`, written over `y`. -/
public def axpy (α : Float) (x y : Float64Array) (h : x.size = y.size) : Float64Array :=
  if hs : y.size < USize.size then
    (inplace y do
      for j in 0...y.usize do
        y[j] := α * x[j] + y[j]).2
  else mapRange y 0 y.size fun j v => α * x[j]! + v

public theorem axpy_eq (α : Float) (x y : Float64Array) (h : x.size = y.size) :
    axpy α x y h = mapRange y 0 y.size fun j v => α * x[j]! + v := by
  unfold axpy
  split
  · rename_i hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [run_forInFrom_map (G := fun j v => α * x[j]! + v)]
    · simp only [Tail.run_done, toNat_usize_of_lt y hs, USize.toNat_zero]
    · intro j hj v
      rw [toNat_usize_of_lt y hs] at hj
      simp [getElem!_pos x j.toNat (by omega)]
  · rfl

/-- `α * x`, written over `x`. -/
public def scal (α : Float) (x : Float64Array) : Float64Array :=
  if hs : x.size < USize.size then
    (inplace x do
      for j in 0...x.usize do
        x[j] := α * x[j]).2
  else mapRange x 0 x.size fun _ v => α * v

public theorem scal_eq (α : Float) (x : Float64Array) :
    scal α x = mapRange x 0 x.size fun _ v => α * v := by
  unfold scal
  split
  · rename_i hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [run_forInFrom_map (G := fun _ v => α * v)]
    · simp only [Tail.run_done, toNat_usize_of_lt x hs, USize.toNat_zero]
    · intro _ _ _; rfl
  · rfl

end Kernel

namespace Vec

variable {n : Nat}

/--
`axpy α x y` is `α * x + y`. It updates `y` in place when `y` is not shared.
-/
public def axpy (α : Float) (x y : Vec n) : Vec n :=
  ⟨Kernel.axpy α x.data y.data (x.size_data.trans y.size_data.symm), by
    rw [Kernel.axpy_eq]; simp [y.size_data]⟩

@[simp] public theorem getElem_axpy (α : Float) (x y : Vec n) (i : Nat) (h : i < n) :
    (axpy α x y)[i] = α * x[i] + y[i] := by
  have := x.size_data; have := y.size_data
  simp only [getElem_def, axpy, Kernel.axpy_eq, getElem_mapRange]
  simp [y.size_data, h, getElem!_pos x.data i (by omega)]

/-- `scal α x` is `α * x`. It updates `x` in place when `x` is not shared. -/
public def scal (α : Float) (x : Vec n) : Vec n :=
  ⟨Kernel.scal α x.data, by rw [Kernel.scal_eq]; simp [x.size_data]⟩

@[simp] public theorem getElem_scal (α : Float) (x : Vec n) (i : Nat) (h : i < n) :
    (scal α x)[i] = α * x[i] := by
  simp only [getElem_def, scal, Kernel.scal_eq, getElem_mapRange]
  simp [x.size_data, h]

/--
`copy x y` is `x`, written over `y` with a single `memmove`, in place when `y` is not shared.
-/
public def copy (x y : Vec n) : Vec n :=
  ⟨x.data.copySlice 0 y.data 0 n, by simp [x.size_data, y.size_data]⟩

@[simp] public theorem getElem_copy (x y : Vec n) (i : Nat) (h : i < n) :
    (copy x y)[i] = x[i] := by
  simp only [getElem_def, copy, getElem_copySlice]
  simp [x.size_data, y.size_data, h]

/-- `swap x y` is `(y, x)`. Nothing is copied. -/
public def swap (x y : Vec n) : Vec n × Vec n := (y, x)

@[simp] public theorem swap_fst (x y : Vec n) : (swap x y).1 = y := by simp [swap]

@[simp] public theorem swap_snd (x y : Vec n) : (swap x y).2 = x := by simp [swap]

/-- The dot product `x[0] * y[0] + … + x[n - 1] * y[n - 1]`, summed from the left. -/
public def dot (x y : Vec n) : Float :=
  foldUpTo n (fun i h s => s + x[i] * y[i]) (fun i h s => s + x.uget i h * y.uget i h) 0

public theorem dot_eq (x y : Vec n) :
    dot x y = Nat.fold n (fun i h s => s + x[i] * y[i]) 0 :=
  foldUpTo_eq _ _ _ (by simp) _

/-- The sum of the absolute values `|x[0]| + … + |x[n - 1]|`, summed from the left. -/
public def asum (x : Vec n) : Float :=
  foldUpTo n (fun i h s => s + x[i].abs) (fun i h s => s + (x.uget i h).abs) 0

public theorem asum_eq (x : Vec n) :
    asum x = Nat.fold n (fun i h s => s + x[i].abs) 0 :=
  foldUpTo_eq _ _ _ (by simp) _

/--
The Euclidean norm `√(x[0] * x[0] + … + x[n - 1] * x[n - 1])`, summed from the left. Unlike the
reference BLAS, it doesn't scale the elements, so the sum may overflow or underflow.
-/
public def nrm2 (x : Vec n) : Float :=
  (foldUpTo n (fun i h s => s + x[i] * x[i]) (fun i h s => s + x.uget i h * x.uget i h) 0).sqrt

public theorem nrm2_eq (x : Vec n) :
    nrm2 x = (Nat.fold n (fun i h s => s + x[i] * x[i]) 0).sqrt := by
  rw [nrm2, foldUpTo_eq _ _ _ (by simp)]

/-- One step of `iamax`: the index and absolute value of the first largest element so far. -/
@[inline, expose] public def iamaxStep (x : Vec n) (i : Nat) (h : i < n) (b : Nat × Float) :
    Nat × Float :=
  let a := x[i].abs
  if i = 0 ∨ a > b.2 then (i, a) else b

/--
The loop of `iamax` from the index `i`, up to the bound `m`, which is `n`, with the index `k` and
absolute value `a` of the first largest element so far. It keeps them in two loop variables rather
than a pair, which would be allocated at every new largest element.
-/
public def iamaxLoop (x : Vec n) (m : USize) (hm : m.toNat = n) (i k : USize) (a : Float) : Nat :=
  if hi : i < m then
    let b := (x.uget i (hm ▸ hi)).abs
    if i = 0 ∨ b > a then iamaxLoop x m hm (i + 1) i b else iamaxLoop x m hm (i + 1) k a
  else k.toNat
termination_by m.toNat - i.toNat
decreasing_by
  all_goals
    rw [USize.lt_iff_toNat_lt] at hi
    have : m.toNat < USize.size := m.toNat_lt_size
    have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
    rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem iamaxLoop_eq (x : Vec n) (m : USize) (hm : m.toNat = n) (i k : USize) (a : Float)
    (j : Nat) (hj : i.toNat = j) (hjn : j ≤ n)
    (hacc : Nat.fold j (fun l hl => iamaxStep x l (by omega)) (0, 0) = (k.toNat, a)) :
    iamaxLoop x m hm i k a = (Nat.fold n (iamaxStep x) (0, 0)).1 := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing i k a j with
  | zero =>
    rw [iamaxLoop, dite_eq_right_of_eq_false (eq_false (by rw [USize.lt_iff_toNat_lt]; omega))]
    obtain rfl : j = n := by omega
    rw [hacc]
  | succ d ih =>
    have hi : i < m := by rw [USize.lt_iff_toNat_lt]; omega
    have hsucc : (i + 1).toNat = j + 1 := by
      have : m.toNat < USize.size := m.toNat_lt_size
      have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      rw [USize.lt_iff_toNat_lt] at hi
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega), hj]
    have hstep : Nat.fold (j + 1) (fun l hl => iamaxStep x l (by omega)) (0, 0) =
        iamaxStep x j (by omega) (k.toNat, a) := by
      rw [Nat.fold_succ, hacc]
    rw [iamaxLoop, dite_eq_left_of_eq_true (eq_true hi)]
    simp only [uget_eq_getElem]
    subst hj
    split
    next hc =>
      refine ih (i + 1) i _ (i.toNat + 1) hsucc (by omega) ?_ (by omega)
      have hc' : i.toNat = 0 ∨ x[i.toNat].abs > a := by simpa [← USize.toNat_inj] using hc
      rw [hstep]
      simp only [iamaxStep, hc', ite_true]
    next hc =>
      refine ih (i + 1) k a (i.toNat + 1) hsucc (by omega) ?_ (by omega)
      have hc' : ¬(i.toNat = 0 ∨ x[i.toNat].abs > a) := by simpa [← USize.toNat_inj] using hc
      rw [hstep]
      simp only [iamaxStep, hc', ite_false]

/--
The index of the first element of largest absolute value, or `0` for the empty vector. As in the
reference BLAS, a `NaN` is never larger, unless it is the first element.
-/
public def iamax (x : Vec n) : Nat :=
  if hn : n < USize.size then iamaxLoop x n.toUSize (by simp [Nat.mod_eq_of_lt hn]) 0 0 0
  else (Nat.fold n (iamaxStep x) (0, 0)).1

public theorem iamax_eq (x : Vec n) : iamax x = (Nat.fold n (iamaxStep x) (0, 0)).1 := by
  unfold iamax
  split
  · exact iamaxLoop_eq x _ _ 0 0 0 0 (by simp) (by omega) (by simp)
  · rfl

end Vec

end BLAS.Float64
