/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# `USize` indices

The arithmetic of `USize` indices that the kernels need: their `toNat` when they don't wrap around,
and the bounds of the column windows of a column-major matrix. These lemmas don't depend on the
element type, so they live in the namespace `BLAS`.

They are private: they are not part of the library's API. The files that need them use
`import all BLAS.Internal`.
-/

namespace BLAS

/-- `(x + y).toNat = x.toNat + y.toNat` when the sum doesn't wrap around. -/
private theorem USize.toNat_add_of_lt {x y : USize} (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by lia)]

/-- `(x * y).toNat = x.toNat * y.toNat` when the product doesn't wrap around. -/
private theorem USize.toNat_mul_of_lt {x y : USize} (h : x.toNat * y.toNat < USize.size) :
    (x * y).toNat = x.toNat * y.toNat := by
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_mul, Nat.mod_eq_of_lt (by lia)]

/-- `(x * y + z).toNat = x.toNat * y.toNat + z.toNat` when it doesn't wrap around. -/
private theorem USize.toNat_mul_add_of_lt {x y z : USize} {X : Nat} (hx : x.toNat = X)
    (h : X * y.toNat + z.toNat < USize.size) : (x * y + z).toNat = X * y.toNat + z.toNat := by
  have hxy : (x * y).toNat = X * y.toNat := by
    rw [USize.toNat_mul_of_lt (by rw [hx]; lia), hx]
  rw [USize.toNat_add_of_lt (by rw [hxy]; lia), hxy]

/-- `(j + 1 + k).toNat = j.toNat + 1 + k.toNat` when the result doesn't wrap around. -/
private theorem USize.toNat_succ_add {j k : USize} (h : j.toNat + 1 + k.toNat < USize.size) :
    (j + 1 + k).toNat = j.toNat + 1 + k.toNat := by
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_add, USize.toNat_add, USize.toNat_one,
    Nat.mod_eq_of_lt (a := j.toNat + 1) (by lia), Nat.mod_eq_of_lt (by lia)]

/-- `(n - j - 1).toNat = n.toNat - j.toNat - 1` for `j < n`: the length of the rest after `j`. -/
private theorem USize.toNat_sub_sub_one {n j : USize} (h : j.toNat < n.toNat) :
    (n - j - 1).toNat = n.toNat - j.toNat - 1 := by
  have h₁ : j ≤ n := USize.le_iff_toNat_le.2 (by lia)
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 ?_), USize.toNat_sub_of_le _ _ h₁,
    USize.toNat_one]
  rw [USize.toNat_sub_of_le _ _ h₁, USize.toNat_one]; lia

/-- `(n - 1 - k).toNat = n.toNat - 1 - k.toNat` for `k < n`: the index of the step `k` down. -/
private theorem USize.toNat_sub_one_sub {n k : USize} (h : k.toNat < n.toNat) :
    (n - 1 - k).toNat = n.toNat - 1 - k.toNat := by
  have h₁ : 1 ≤ n := USize.le_iff_toNat_le.2 (by rw [USize.toNat_one]; lia)
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 ?_), USize.toNat_sub_of_le _ _ h₁,
    USize.toNat_one]
  rw [USize.toNat_sub_of_le _ _ h₁, USize.toNat_one]; lia

/-! ## Columns of a matrix -/

/-- `(m * j).toNat + m.toNat ≤ p` for `j < n` and `m * n ≤ p < USize.size`: column `j` fits. -/
private theorem toNat_mul_add_le {m j : USize} {n p : Nat} (hj : j.toNat < n)
    (hmn : m.toNat * n ≤ p) (hp : p < USize.size) : (m * j).toNat + m.toNat ≤ p := by
  have h1 : m.toNat * (j.toNat + 1) ≤ m.toNat * n := Nat.mul_le_mul_left _ hj
  rw [Nat.mul_succ] at h1
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_mul, Nat.mod_eq_of_lt (by lia)]
  lia

/--
The window of `len` elements at `x * y + z` fits in an `X × Y` matrix, for `y < Y` and
`z + len ≤ X`.
-/
private theorem toNat_mul_add_add_le {x y z len : USize} {X Y : Nat} (hx : x.toNat = X)
    (hy : y.toNat < Y) (hz : z.toNat + len.toNat ≤ X) (hs : X * Y < USize.size) :
    (x * y + z).toNat + len.toNat ≤ X * Y := by
  have h1 : X * (y.toNat + 1) ≤ X * Y := Nat.mul_le_mul_left _ hy
  rw [Nat.mul_succ] at h1
  rw [USize.toNat_mul_add_of_lt hx (by lia)]
  lia

/-- `(x * y + z).toNat` for an element `z ≤ X` of the column `y < Y` of an `X × Y` matrix. -/
private theorem toNat_mul_add_eq {x y z : USize} {X Y : Nat} (hx : x.toNat = X) (hy : y.toNat < Y)
    (hz : z.toNat ≤ X) (hs : X * Y < USize.size) : (x * y + z).toNat = X * y.toNat + z.toNat :=
  USize.toNat_mul_add_of_lt hx (by
    have h1 : X * (y.toNat + 1) ≤ X * Y := Nat.mul_le_mul_left _ hy
    rw [Nat.mul_succ] at h1; lia)

end BLAS
