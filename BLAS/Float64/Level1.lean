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

Each routine runs a loop over the `USize` indices `off + inc * i` of its vectors when their arrays'
sizes fit in a `USize`, as they do for every array in memory, and its model otherwise, so that its
specification needs no hypothesis on the size. The loops are the same for every stride: at stride
`1` they run as fast as loops over contiguous indices.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Vec

variable {n : Nat}

/--
A vector `v` whose array is the array of `w` with the element `i` mapped by `g i`, at the same
indices, has the elements `g i w[i]`.
-/
public theorem getElem_of_data_eq_modifyAt {v w : Vec n} (g : Nat → Float → Float)
    (hd : v.data = w.data.modifyAt w.stride.idx 0 n g) (ho : v.off = w.off)
    (hc : v.inc = w.inc) (i : Nat) (h : i < n) : v[i] = g i w[i] := by
  simp only [getElem_def]
  have e : v.data[v.off + v.inc * i]'(v.index_lt h) =
      (w.data.modifyAt w.stride.idx 0 n g)[w.stride.idx i]'(by
        rw [size_modifyAt]; exact w.index_lt h) := by
    simp only [hd, ho, hc, idx_stride]
  rw [e, getElem_modifyAt_stride _ w.fits (Nat.le_refl _) _ (Nat.zero_le _) h]
  rfl

/--
The element `i` of a `modifyAt` at the indices of a vector, on an array of the size of the
vector's array.
-/
public theorem getElem_modifyAt_stride (x : Vec n) {a : Float64Array} (ha : a.size = x.data.size)
    {lo hi : Nat} (hn : hi ≤ n) (g : Nat → Float → Float) {i : Nat} (h₁ : lo ≤ i) (h₂ : i < hi)
    (h : x.off + x.inc * i < (a.modifyAt x.stride.idx lo hi g).size) :
    (a.modifyAt x.stride.idx lo hi g)[x.off + x.inc * i] =
      g i (a[x.off + x.inc * i]'(by simpa using h)) :=
  Float64Array.getElem_modifyAt_stride a (by rw [ha]; exact x.fits) hn g h₁ h₂

/-- The number of elements `n` as a `USize`, in a vector whose array has a `USize` size. -/
public theorem toNat_toUSize (x : Vec n) (hs : x.data.size < USize.size) : n.toUSize.toNat = n := by
  have := x.le_size
  grind

/-- The `USize` indices of the loop of a vector update, from the step `0`, don't wrap. -/
public theorem loop_idx (x : Vec n) (hs : x.data.size < USize.size) :
    ∀ j : USize, (0 : USize).toNat ≤ j.toNat → j.toNat < n.toUSize.toNat →
      (x.off.toUSize + x.inc.toUSize * j).toNat = x.stride.idx j.toNat := by
  rw [x.toNat_toUSize hs]
  exact fun j _ hj => x.toNat_index hs hj

/-- The array of `axpy`. -/
public def axpyData (α : Float) (x y : Vec n) : Float64Array :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2
    let a := y.data
    let o := y.off.toUSize
    let c := y.inc.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    (inplace a do
      for k in 0...nu do
        have hk : (o + c * k).toNat < a.size := y.toNat_index_lt hs.2 (by lia)
        a[o + c * k] := α * x.uget xo xc rfl rfl hs.1 k (by lia) + a[o + c * k]).2
  else y.data.modifyAt y.stride.idx 0 n fun i v => α * x.data[x.off + x.inc * i]! + v

public theorem axpyData_eq (α : Float) (x y : Vec n) :
    axpyData α x y = y.data.modifyAt y.stride.idx 0 n
      fun i v => α * x.data[x.off + x.inc * i]! + v := by
  unfold axpyData
  split
  · rename_i hs
    have he := y.loop_idx hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := fun i v => α * x.data[x.off + x.inc * i]! + v) (he := he)]
    · simp only [Tail.run_done, y.toNat_toUSize hs.2, USize.toNat_zero]
    · intro j _ hj v
      rw [y.toNat_toUSize hs.2] at hj
      rw [getElem!_pos x.data (x.off + x.inc * j.toNat) (x.index_lt hj)]
      simp [getElem_def]
  · rfl

/--
`axpy α x y` is `α * x + y`. It updates `y` in place when its array is not shared, and leaves the
elements of the array outside `y` unchanged.
-/
@[expose] public def axpy (α : Float) (x y : Vec n) : Vec n where
  data := axpyData α x y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [axpyData_eq, size_modifyAt]; exact y.bound

/-- The array of `axpy α x y` is the array of `y` with its elements updated. -/
public theorem data_axpy (α : Float) (x y : Vec n) :
    (axpy α x y).data = y.data.modifyAt y.stride.idx 0 n
      fun i v => α * x.data[x.off + x.inc * i]! + v :=
  axpyData_eq α x y

@[simp] public theorem off_axpy (α : Float) (x y : Vec n) : (axpy α x y).off = y.off := rfl

@[simp] public theorem inc_axpy (α : Float) (x y : Vec n) : (axpy α x y).inc = y.inc := rfl

@[simp] public theorem getElem_axpy (α : Float) (x y : Vec n) (i : Nat) (h : i < n) :
    (axpy α x y)[i] = α * x[i] + y[i] := by
  rw [getElem_of_data_eq_modifyAt _ (data_axpy α x y) rfl rfl i h,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt h)]
  rfl

/-- The array of `scal`. -/
public def scalData (α : Float) (x : Vec n) : Float64Array :=
  if hs : x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    (inplace a do
      for k in 0...nu do
        have hk : (o + c * k).toNat < a.size := x.toNat_index_lt hs (by lia)
        a[o + c * k] := α * a[o + c * k]).2
  else x.data.modifyAt x.stride.idx 0 n fun _ v => α * v

public theorem scalData_eq (α : Float) (x : Vec n) :
    scalData α x = x.data.modifyAt x.stride.idx 0 n fun _ v => α * v := by
  unfold scalData
  split
  · rename_i hs
    have he := x.loop_idx hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := fun _ v => α * v) (he := he)]
    · simp only [Tail.run_done, x.toNat_toUSize hs, USize.toNat_zero]
    · intro _ _ _ _; rfl
  · rfl

/--
`scal α x` is `α * x`. It updates `x` in place when its array is not shared, and leaves the
elements of the array outside `x` unchanged.
-/
@[expose] public def scal (α : Float) (x : Vec n) : Vec n where
  data := scalData α x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [scalData_eq, size_modifyAt]; exact x.bound

/-- The array of `scal α x` is the array of `x` with its elements updated. -/
public theorem data_scal (α : Float) (x : Vec n) :
    (scal α x).data = x.data.modifyAt x.stride.idx 0 n fun _ v => α * v :=
  scalData_eq α x

@[simp] public theorem off_scal (α : Float) (x : Vec n) : (scal α x).off = x.off := rfl

@[simp] public theorem inc_scal (α : Float) (x : Vec n) : (scal α x).inc = x.inc := rfl

@[simp] public theorem getElem_scal (α : Float) (x : Vec n) (i : Nat) (h : i < n) :
    (scal α x)[i] = α * x[i] :=
  getElem_of_data_eq_modifyAt _ (data_scal α x) rfl rfl i h

/--
The array of `copy`: a single `memmove` for contiguous vectors, and a loop over the strides
otherwise.
-/
public def copyData (x y : Vec n) : Float64Array :=
  if x.inc = 1 ∧ y.inc = 1 then x.data.copySlice x.off y.data y.off n
  else if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2
    let a := y.data
    let o := y.off.toUSize
    let c := y.inc.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    (inplace a do
      for k in 0...nu do
        have hk : (o + c * k).toNat < a.size := y.toNat_index_lt hs.2 (by lia)
        a[o + c * k] := x.uget xo xc rfl rfl hs.1 k (by lia)).2
  else y.data.modifyAt y.stride.idx 0 n fun i _ => x.data[x.off + x.inc * i]!

public theorem copyData_eq (x y : Vec n) :
    copyData x y = y.data.modifyAt y.stride.idx 0 n
      fun i _ => x.data[x.off + x.inc * i]! := by
  unfold copyData
  split
  · rename_i hc
    rcases Nat.eq_zero_or_pos n with h₀ | h₀
    · subst h₀
      rw [modifyAt_self]
      apply ext_getElem (by simp [size_copySlice]; lia)
      intro p _ _
      rw [getElem_copySlice]
      split
      · rfl
      · rw [dite_eq_right (by lia)]
    · have hw : ∀ v : Vec n, v.inc = 1 → v.off + n ≤ v.data.size := by
        intro v h
        have := v.index_lt (i := n - 1) (by lia); simp [h] at this; lia
      rw [copySlice_eq_modifyAt _ _ _ _ _ _ (hw x hc.1) (hw y hc.2)]
      exact modifyAt_congr _ (fun i _ _ => by simp [idx_stride, hc.2])
        (fun i _ _ => by simp [hc.1])
  split
  · rename_i hs
    have he := y.loop_idx hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_write (G := fun i => x.data[x.off + x.inc * i]!) (he := he)]
    · simp only [Tail.run_done, y.toNat_toUSize hs.2, USize.toNat_zero]
    · intro j _ hj
      rw [y.toNat_toUSize hs.2] at hj
      rw [getElem!_pos x.data (x.off + x.inc * j.toNat) (x.index_lt hj)]
      simp [getElem_def]
  · rfl

/--
`copy x y` is `x`, written over `y`, in place when the array of `y` is not shared. It leaves the
elements of the array outside `y` unchanged.
-/
@[expose] public def copy (x y : Vec n) : Vec n where
  data := copyData x y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [copyData_eq, size_modifyAt]; exact y.bound

/-- The array of `copy x y` is the array of `y` with its elements replaced. -/
public theorem data_copy (x y : Vec n) :
    (copy x y).data = y.data.modifyAt y.stride.idx 0 n
      fun i _ => x.data[x.off + x.inc * i]! :=
  copyData_eq x y

@[simp] public theorem off_copy (x y : Vec n) : (copy x y).off = y.off := rfl

@[simp] public theorem inc_copy (x y : Vec n) : (copy x y).inc = y.inc := rfl

@[simp] public theorem getElem_copy (x y : Vec n) (i : Nat) (h : i < n) :
    (copy x y)[i] = x[i] := by
  rw [getElem_of_data_eq_modifyAt _ (data_copy x y) rfl rfl i h,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt h)]
  rfl

/-- `swap x y` is `(y, x)`. Nothing is copied. -/
public def swap (x y : Vec n) : Vec n × Vec n := (y, x)

@[simp] public theorem swap_fst (x y : Vec n) : (swap x y).1 = y := by simp [swap]

@[simp] public theorem swap_snd (x y : Vec n) : (swap x y).2 = x := by simp [swap]

/-- The dot product `x[0] * y[0] + … + x[n - 1] * y[n - 1]`, summed from the left. -/
public def dot (x y : Vec n) : Float :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    let yo := y.off.toUSize
    let yc := y.inc.toUSize
    foldUpTo n (fun i h s => s + x[i] * y[i])
      (fun i h s => s + x.uget xo xc rfl rfl hs.1 i h * y.uget yo yc rfl rfl hs.2 i h) 0
  else Nat.fold n (fun i h s => s + x[i] * y[i]) 0

public theorem dot_eq (x y : Vec n) :
    dot x y = Nat.fold n (fun i h s => s + x[i] * y[i]) 0 := by
  unfold dot; split
  · exact foldUpTo_eq _ _ _ (by simp) _
  · rfl

/-- The sum of the absolute values `|x[0]| + … + |x[n - 1]|`, summed from the left. -/
public def asum (x : Vec n) : Float :=
  if hs : x.data.size < USize.size then
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    foldUpTo n (fun i h s => s + x[i].abs) (fun i h s => s + (x.uget xo xc rfl rfl hs i h).abs) 0
  else Nat.fold n (fun i h s => s + x[i].abs) 0

public theorem asum_eq (x : Vec n) :
    asum x = Nat.fold n (fun i h s => s + x[i].abs) 0 := by
  unfold asum; split
  · exact foldUpTo_eq _ _ _ (by simp) _
  · rfl

/--
The Euclidean norm `√(x[0] * x[0] + … + x[n - 1] * x[n - 1])`, summed from the left. Unlike the
reference BLAS, it doesn't scale the elements, so the sum may overflow or underflow.
-/
public def nrm2 (x : Vec n) : Float :=
  if hs : x.data.size < USize.size then
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    (foldUpTo n (fun i h s => s + x[i] * x[i])
      (fun i h s => s + x.uget xo xc rfl rfl hs i h * x.uget xo xc rfl rfl hs i h) 0).sqrt
  else (Nat.fold n (fun i h s => s + x[i] * x[i]) 0).sqrt

public theorem nrm2_eq (x : Vec n) :
    nrm2 x = (Nat.fold n (fun i h s => s + x[i] * x[i]) 0).sqrt := by
  unfold nrm2; split
  · simp only []
    rw [foldUpTo_eq _ _ _ (by simp)]
  · rfl

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
public def iamaxLoop (x : Vec n) (o c : USize) (ho : x.off.toUSize = o) (hc : x.inc.toUSize = c)
    (hs : x.data.size < USize.size) (m : USize) (hm : m.toNat = n) (i k : USize) (a : Float) : Nat :=
  if hi : i < m then
    let b := (x.uget o c ho hc hs i (hm ▸ hi)).abs
    if i = 0 ∨ b > a then iamaxLoop x o c ho hc hs m hm (i + 1) i b
    else iamaxLoop x o c ho hc hs m hm (i + 1) k a
  else k.toNat
termination_by m.toNat - i.toNat
decreasing_by
  all_goals
    grind

private theorem iamaxLoop_eq (x : Vec n) (o c : USize) (ho : x.off.toUSize = o)
    (hc : x.inc.toUSize = c) (hs : x.data.size < USize.size) (m : USize) (hm : m.toNat = n) (i k : USize) (a : Float)
    (j : Nat) (hj : i.toNat = j) (hjn : j ≤ n)
    (hacc : Nat.fold j (fun l hl => iamaxStep x l (by lia)) (0, 0) = (k.toNat, a)) :
    iamaxLoop x o c ho hc hs m hm i k a = (Nat.fold n (iamaxStep x) (0, 0)).1 := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing i k a j with
  | zero =>
    rw [iamaxLoop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : j = n := by lia
    rw [hacc]
  | succ d ih =>
    have hi : i < m := by grind
    have hsucc : (i + 1).toNat = j + 1 := by grind
    have hstep : Nat.fold (j + 1) (fun l hl => iamaxStep x l (by lia)) (0, 0) =
        iamaxStep x j (by lia) (k.toNat, a) := by
      rw [Nat.fold_succ, hacc]
    rw [iamaxLoop, dite_eq_left_of_eq_true (eq_true hi)]
    simp only [uget_eq_getElem]
    subst hj
    split
    next hc =>
      refine ih (i + 1) i _ (i.toNat + 1) hsucc (by lia) ?_ (by lia)
      have hc' : i.toNat = 0 ∨ x[i.toNat].abs > a := by simpa [← USize.toNat_inj] using hc
      rw [hstep]
      simp only [iamaxStep, hc', ite_true]
    next hc =>
      refine ih (i + 1) k a (i.toNat + 1) hsucc (by lia) ?_ (by lia)
      have hc' : ¬(i.toNat = 0 ∨ x[i.toNat].abs > a) := by simpa [← USize.toNat_inj] using hc
      rw [hstep]
      simp only [iamaxStep, hc', ite_false]

/--
The index of the first element of largest absolute value, or `0` for the empty vector. As in the
reference BLAS, a `NaN` is never larger, unless it is the first element.
-/
public def iamax (x : Vec n) : Nat :=
  if hs : x.data.size < USize.size then iamaxLoop x _ _ rfl rfl hs n.toUSize (x.toNat_toUSize hs) 0 0 0
  else (Nat.fold n (iamaxStep x) (0, 0)).1

public theorem iamax_eq (x : Vec n) : iamax x = (Nat.fold n (iamaxStep x) (0, 0)).1 := by
  unfold iamax
  split
  · exact iamaxLoop_eq x _ _ rfl rfl _ _ _ 0 0 0 0 (by simp) (by lia) (by simp)
  · rfl

end Vec

end BLAS.Float64
