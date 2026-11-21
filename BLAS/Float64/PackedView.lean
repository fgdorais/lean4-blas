/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.View
public import BLAS.Float64.Tpmv
public import BLAS.Float64.Tpsv
public import BLAS.Float64.Spmv
public import BLAS.Float64.Spr

/-!
# Packed views

The views of a vector `ap : Vec (n * (n + 1) / 2)` that holds a triangle of an `n × n` matrix
packed by columns, as in the reference BLAS, for `blas%`: `ap.upperPacked`, `ap.unitLowerPacked`,
… (`TriPacked`) are the triangular matrices, which select `tpmv` and `tpsv`, and `tpmvT` and
`tpsvT` for their transposes; and `ap.symUpperPacked` and `ap.symLowerPacked` (`SymPacked`) are
the symmetric matrices, which select `spmv`, and `spr` and `spr2` as targets. As for the other
views, a view is the vector itself, with no copy, and its field `mat` is the vector.

The element `i, j` of a view is the element of the matrix, from its packed triangle: `0` outside
the triangle and `1` on a unit diagonal for a triangular matrix, and the element `j, i` of the
triangle outside it for a symmetric matrix.
-/

open ScalarArray

namespace BLAS.Float64

/--
The triangular matrix whose triangle `uplo` is packed in `mat`, with a unit diagonal if `d` is
`.unit`: the element `i ≤ j` of the upper triangle is `mat[upIdx j i]`, and the element `i ≥ j` of
the lower triangle is `mat[loIdx n j i]`. The routines don't read the diagonal when it is unit.
-/
public structure TriPacked (uplo : Uplo) (d : Diag) (n : Nat) where
  /-- The packed triangle. -/
  mat : Vec (n * (n + 1) / 2)

/-- The symmetric matrix whose triangle `uplo` is packed in `mat`, as for `TriPacked`. -/
public structure SymPacked (uplo : Uplo) (n : Nat) where
  /-- The packed triangle. -/
  mat : Vec (n * (n + 1) / 2)

namespace Vec

variable {n : Nat}

/-- The upper triangular matrix packed in `ap`, with its diagonal. -/
@[expose] public def upperPacked (ap : Vec (n * (n + 1) / 2)) : TriPacked .upper .nonUnit n := ⟨ap⟩

/-- The lower triangular matrix packed in `ap`, with its diagonal. -/
@[expose] public def lowerPacked (ap : Vec (n * (n + 1) / 2)) : TriPacked .lower .nonUnit n := ⟨ap⟩

/-- The upper triangular matrix packed in `ap`, with a unit diagonal, which isn't read. -/
@[expose] public def unitUpperPacked (ap : Vec (n * (n + 1) / 2)) : TriPacked .upper .unit n :=
  ⟨ap⟩

/-- The lower triangular matrix packed in `ap`, with a unit diagonal, which isn't read. -/
@[expose] public def unitLowerPacked (ap : Vec (n * (n + 1) / 2)) : TriPacked .lower .unit n :=
  ⟨ap⟩

/-- The symmetric matrix with the upper triangle packed in `ap`. -/
@[expose] public def symUpperPacked (ap : Vec (n * (n + 1) / 2)) : SymPacked .upper n := ⟨ap⟩

/-- The symmetric matrix with the lower triangle packed in `ap`. -/
@[expose] public def symLowerPacked (ap : Vec (n * (n + 1) / 2)) : SymPacked .lower n := ⟨ap⟩

@[simp] public theorem upperPacked_eq (ap : Vec (n * (n + 1) / 2)) :
    ap.upperPacked = TriPacked.mk ap := rfl

@[simp] public theorem lowerPacked_eq (ap : Vec (n * (n + 1) / 2)) :
    ap.lowerPacked = TriPacked.mk ap := rfl

@[simp] public theorem unitUpperPacked_eq (ap : Vec (n * (n + 1) / 2)) :
    ap.unitUpperPacked = TriPacked.mk ap := rfl

@[simp] public theorem unitLowerPacked_eq (ap : Vec (n * (n + 1) / 2)) :
    ap.unitLowerPacked = TriPacked.mk ap := rfl

@[simp] public theorem symUpperPacked_eq (ap : Vec (n * (n + 1) / 2)) :
    ap.symUpperPacked = SymPacked.mk ap := rfl

@[simp] public theorem symLowerPacked_eq (ap : Vec (n * (n + 1) / 2)) :
    ap.symLowerPacked = SymPacked.mk ap := rfl

end Vec

/-! ## Elements -/

/--
`T[(i, j)]` is the element of the triangular matrix: its packed element in the triangle, `1` on a
unit diagonal, and `0` outside the triangle.
-/
public instance {uplo : Uplo} {d : Diag} {n : Nat} :
    GetElem (TriPacked uplo d n) (Nat × Nat) Float fun _ p => p.1 < n ∧ p.2 < n where
  getElem T p h :=
    if p.1 = p.2 ∧ d = .unit then 1
    else match uplo with
      | .upper => if h' : p.1 ≤ p.2 then T.mat[upIdx p.2 p.1]'(upIdx_lt h' h.2) else 0
      | .lower => if h' : p.2 ≤ p.1 then T.mat[loIdx n p.2 p.1]'(loIdx_lt h' h.1) else 0

/--
`S[(i, j)]` is the element of the symmetric matrix: the packed element `i, j` in the triangle, and
the packed element `j, i` outside it.
-/
public instance {uplo : Uplo} {n : Nat} : GetElem (SymPacked uplo n) (Nat × Nat) Float
    fun _ p => p.1 < n ∧ p.2 < n where
  getElem S p h :=
    match uplo with
    | .upper => S.mat[upIdx (max p.1 p.2) (min p.1 p.2)]'(upIdx_lt (by lia) (by lia))
    | .lower => S.mat[loIdx n (min p.1 p.2) (max p.1 p.2)]'(loIdx_lt (by lia) (by lia))

/-! ## Instances -/

/-- `α * S * x + β * y` is `spmv`. -/
public instance {uplo : Uplo} {n : Nat} : MulAdd Float (SymPacked uplo n) (Vec n) (Vec n) where
  run α S x β y := Mat.spmv uplo α S.mat x β y

/-- `T * x` is `tpmv`. -/
public instance {uplo : Uplo} {d : Diag} {n : Nat} : MulIn (TriPacked uplo d n) (Vec n) where
  run T x := Mat.tpmv uplo d T.mat x

/-- `Tᵀ * x` is `tpmvT`. -/
public instance {uplo : Uplo} {d : Diag} {n : Nat} :
    MulIn (Transpose (TriPacked uplo d n)) (Vec n) where
  run T x := Mat.tpmvT uplo d T.mat.mat x

/-- `T⁻¹ * x` is `tpsv`. -/
public instance {uplo : Uplo} {d : Diag} {n : Nat} : Solve (TriPacked uplo d n) (Vec n) where
  run T x := Mat.tpsv uplo d T.mat x

/-- `Tᵀ⁻¹ * x` is `tpsvT`. -/
public instance {uplo : Uplo} {d : Diag} {n : Nat} :
    Solve (Transpose (TriPacked uplo d n)) (Vec n) where
  run T x := Mat.tpsvT uplo d T.mat.mat x

/-- `α * x * xᵀ + S` is `spr`. -/
public instance {uplo : Uplo} {n : Nat} : RankKAcc Float (Vec n) (SymPacked uplo n) where
  run α x S := ⟨Mat.spr uplo α x S.mat⟩

/-- `α * x * yᵀ + α * y * xᵀ + S` is `spr2`. -/
public instance {uplo : Uplo} {n : Nat} : Rank2KAcc Float (Vec n) (SymPacked uplo n) where
  run α x y S := ⟨Mat.spr2 uplo α x y S.mat⟩

/-! ## The routines of the instances -/

section

variable {n : Nat} {uplo : Uplo} {d : Diag}

@[simp] public theorem mulAdd_symPacked_vec (α : Float) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (β : Float) (y : Vec n) :
    MulAdd.run α (SymPacked.mk (uplo := uplo) ap) x β y = Mat.spmv uplo α ap x β y := rfl

@[simp] public theorem mulIn_triPacked_vec (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    MulIn.run (TriPacked.mk (uplo := uplo) (d := d) ap) x = Mat.tpmv uplo d ap x := rfl

@[simp] public theorem mulIn_transpose_triPacked_vec (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    MulIn.run (Transpose.mk (TriPacked.mk (uplo := uplo) (d := d) ap)) x = Mat.tpmvT uplo d ap x :=
  rfl

@[simp] public theorem solve_triPacked_vec (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Solve.run (TriPacked.mk (uplo := uplo) (d := d) ap) x = Mat.tpsv uplo d ap x := rfl

@[simp] public theorem solve_transpose_triPacked_vec (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    Solve.run (Transpose.mk (TriPacked.mk (uplo := uplo) (d := d) ap)) x = Mat.tpsvT uplo d ap x :=
  rfl

@[simp] public theorem rankKAcc_vec_symPacked (α : Float) (x : Vec n)
    (ap : Vec (n * (n + 1) / 2)) :
    RankKAcc.run α x (SymPacked.mk (uplo := uplo) ap) = SymPacked.mk (Mat.spr uplo α x ap) := rfl

@[simp] public theorem rank2KAcc_vec_symPacked (α : Float) (x y : Vec n)
    (ap : Vec (n * (n + 1) / 2)) :
    Rank2KAcc.run α x y (SymPacked.mk (uplo := uplo) ap) =
      SymPacked.mk (Mat.spr2 uplo α x y ap) := rfl

end

end BLAS.Float64
