/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# `USize` indices

The bounds of the column windows of a column-major matrix, for `USize` indices. They are
nonlinear, so `grind` needs the bound `X * y + X ≤ X * Y` spelled out. The linear `toNat` facts
about `USize` indices that don't wrap around are left to `grind` where they are used. These lemmas
don't depend on the element type, so they live in the namespace `BLAS`.

They are private: they are not part of the library's API. The files that need them use
`import all BLAS.Internal`.
-/

namespace BLAS

/--
`(j + 1 + k).toNat = j.toNat + 1 + k.toNat` when the result doesn't wrap around. This is a `grind`
fact, but a `grind` proof inside an `inplace` loop body captures the loop's state and stops the loop
lemmas from matching, so inner loop bodies use this lemma instead.
-/
private theorem toNat_succ_add {j k : USize} (h : j.toNat + 1 + k.toNat < USize.size) :
    (j + 1 + k).toNat = j.toNat + 1 + k.toNat := by
  grind

/--
`(m * j).toNat + m.toNat ≤ p` for `j < n` and `m * n ≤ p`: column `j` fits. A product that wraps
around only gets smaller, so this needs no bound on `p`.
-/
private theorem toNat_mul_add_le {m j : USize} {n p : Nat} (hj : j.toNat < n)
    (hmn : m.toNat * n ≤ p) : (m * j).toNat + m.toNat ≤ p := by
  have : m.toNat * j.toNat + m.toNat ≤ m.toNat * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  grind

/--
The window of `len` elements at `x * y + z` fits in an `X × Y` matrix, for `y < Y` and
`z + len ≤ X`. As for `toNat_mul_add_le`, this needs no bound on `X * Y`.
-/
private theorem toNat_mul_add_add_le {x y z len : USize} {X Y : Nat} (hx : x.toNat = X)
    (hy : y.toNat < Y) (hz : z.toNat + len.toNat ≤ X) :
    (x * y + z).toNat + len.toNat ≤ X * Y := by
  have : X * y.toNat + X ≤ X * Y := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  grind

/-- `(x * y + z).toNat` for an element `z ≤ X` of the column `y < Y` of an `X × Y` matrix. -/
private theorem toNat_mul_add_eq {x y z : USize} {X Y : Nat} (hx : x.toNat = X) (hy : y.toNat < Y)
    (hz : z.toNat ≤ X) (hs : X * Y < USize.size) : (x * y + z).toNat = X * y.toNat + z.toNat := by
  have : X * y.toNat + X ≤ X * Y := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  grind

/-- The elements of two distinct columns of a column-major matrix are at distinct indices. -/
private theorem col_index_ne {off ld m i j i' j' : Nat} (hi : i < m) (hi' : i' < m) (hml : m ≤ ld)
    (hj : j ≠ j') : off + ld * j + i ≠ off + ld * j' + i' := by
  rcases Nat.lt_or_gt_of_ne hj with h | h
  · have : ld * (j + 1) ≤ ld * j' := Nat.mul_le_mul_left _ h
    rw [Nat.mul_succ] at this; lia
  · have : ld * (j' + 1) ≤ ld * j := Nat.mul_le_mul_left _ h
    rw [Nat.mul_succ] at this; lia

/-- The steps of a stride of `1`, such as the rows of a column of a matrix, are distinct. -/
private theorem col_injOn (o lo hi : Nat) :
    ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi →
      (ScalarArray.Stride.mk o 1).idx i = (ScalarArray.Stride.mk o 1).idx j → i = j :=
  fun _ _ _ _ _ _ e => by simp only [ScalarArray.Stride.idx] at e; lia

end BLAS
