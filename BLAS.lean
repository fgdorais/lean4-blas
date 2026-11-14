/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray
public import ScalarArray.Notation
public import BLAS.Float64
public import BLAS.Float32

/-!
# BLAS

Basic Linear Algebra Subprograms written in Lean, on the unboxed arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays), with no C code of its own.
The routines come with proved specifications, and their speed is measured by `lake exe bench`.
-/
