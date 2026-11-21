/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Gbmv
import all BLAS.Internal

/-!
# Packed triangles

The packed routines of the reference BLAS (`dspmv`, `dtpmv`, `dtpsv`, `dspr` and `dspr2`) take a
triangle of an `n × n` matrix packed by columns in a vector of `n * (n + 1) / 2` elements, here a
`Vec (n * (n + 1) / 2)`, which may have an offset and a stride. For the upper triangle, column `j`
holds the elements `0, …, j` and starts at `j * (j + 1) / 2`, so the element `i ≤ j` is at
`upIdx j i`; for the lower triangle, column `j` holds the elements `j, …, n - 1`, after the
`n - j + 1, …, n` elements of the columns before it, so the element `i ≥ j` is at `loIdx n j i`.
-/

namespace BLAS.Float32

/-- The index of the element `i ≤ j` of column `j` of a packed upper triangle. -/
@[expose] public def upIdx (j i : Nat) : Nat := j * (j + 1) / 2 + i

/-- The index of the element `i ≥ j` of column `j` of a packed lower triangle of order `n`. -/
@[expose] public def loIdx (n j i : Nat) : Nat :=
  n * (n + 1) / 2 - (n - j) * (n - j + 1) / 2 + (i - j)

/-- The element `i ≤ j < n` of a packed upper triangle is inside it. -/
public theorem upIdx_lt {n i j : Nat} (hij : i ≤ j) (hj : j < n) : upIdx j i < n * (n + 1) / 2 :=
  tri_upper_lt hij hj

/-- The element `j ≤ i < n` of a packed lower triangle is inside it. -/
public theorem loIdx_lt {n i j : Nat} (hji : j ≤ i) (hi : i < n) : loIdx n j i < n * (n + 1) / 2 :=
  tri_lower_lt hji hi

/-- A packed triangle in an array with a `USize` size has a `USize` size. -/
public theorem tri_lt_size {n : Nat} (ap : Vec (n * (n + 1) / 2)) (hs : ap.data.size < USize.size) :
    n * (n + 1) / 2 < USize.size :=
  Nat.lt_of_le_of_lt ap.le_size hs

end BLAS.Float32
