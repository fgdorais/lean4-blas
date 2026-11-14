/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
import BLASTest.Util
meta import BLAS
meta import BLASTest.Util

/-!
Tests for `gemm`, `syrk`, `syrkT`, `trsm` and `trsmRight` on `Float32`.
-/

open BLAS.Float32

/-- An `m × n` matrix of small integers computed from the indices and the seed `s`. -/
def mat (m n : Nat) (s : Nat := 0) : Mat m n :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat32 - 5

/-- The elements of `gemmEntry`, column after column. -/
def gemmModelList (α : Float32) (A : Mat m k) (B : Mat k n) (β : Float32) (C : Mat m n) :
    List Float32 :=
  (List.ofFn fun j : Fin n => List.ofFn fun i : Fin m =>
    Mat.gemmEntry α A B β C i.val j.val i.isLt j.isLt).flatten

/--
The address of the array of `A`, with `A`. It is not inlined, so the address is taken before `A`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (A : Mat m n) : USize × Mat m n := (BLASTest.addr A.data, A)

/-- Whether `gemm` computes its model exactly, for these shapes. -/
def gemmMatchesModel (m n k : Nat) (α β : Float32) : Bool :=
  let A := mat m k 1
  let B := mat k n 2
  let C := mat m n 3
  (Mat.gemm α A B β C).toList == gemmModelList α A B β C

/-! ## `gemm` -/

-- `[[1, 2], [3, 4]] * [[5, 6], [7, 8]] = [[19, 22], [43, 50]]`, in column-major order.
#guard
  let A : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := Mat.ofPMat ⟨.ofList [5, 7, 6, 8], by decide⟩
  let C : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 1, 1, 1], by decide⟩
  (Mat.gemm 1 A B 0 C).toList == [19, 43, 22, 50] &&
    (Mat.gemm 2 A B 1 C).toList == [39, 87, 45, 101]

-- A `2 × 3` times a `3 × 1`.
#guard
  let A : Mat 2 3 := Mat.ofPMat ⟨.ofList [1, 4, 2, 5, 3, 6], by decide⟩
  let B : Mat 3 1 := Mat.ofPMat ⟨.ofList [1, 0, -1], by decide⟩
  let C : Mat 2 1 := Mat.ofPMat ⟨.ofList [10, 20], by decide⟩
  (Mat.gemm 1 A B (-1) C).toList == [-12, -22]

#guard gemmMatchesModel 5 4 3 1.5 0.5
#guard gemmMatchesModel 1 1 1 2 3
#guard gemmMatchesModel 17 9 13 (-0.25) 2
#guard gemmMatchesModel 32 33 31 1 1

-- Empty shapes: with `k = 0`, `gemm` is `β * C`.
#guard gemmMatchesModel 0 3 2 1 1
#guard gemmMatchesModel 3 0 2 1 1
#guard gemmMatchesModel 3 2 0 1 2
#guard (Mat.gemm 1 (mat 3 0) (mat 0 2) 2 (mat 3 2)).toList == (mat 3 2).toList.map (2 * ·)

#guard gemmMatchesModel 5 4 3 0 0.5
#guard gemmMatchesModel 5 4 3 1.5 0
#guard gemmMatchesModel 5 4 3 0 0

-- As in the reference BLAS, `β = 0` sets `C` to `0` without reading it, so a `NaN` in `C` goes.
#guard
  let C : Mat 1 1 := Mat.ofPMat ⟨.ofList [0 / 0], by decide⟩
  (Mat.gemm 1 (mat 1 1) (mat 1 1) 0 C).toList == [(mat 1 1)[(0, 0)] * (mat 1 1)[(0, 0)]] &&
    (Mat.gemmNaive 1 (mat 1 1) (mat 1 1) 0 C).toList == [(mat 1 1)[(0, 0)] * (mat 1 1)[(0, 0)]]

-- `α = 0` only scales `C`, without reading `A` or `B`.
#guard
  let A : Mat 1 1 := .ofFn fun _ _ => 0 / 0
  let C : Mat 1 1 := .ofFn fun _ _ => 3
  (Mat.gemm 0 A A 2 C).toList == [6] && (Mat.gemmNaive 0 A A 0 C).toList == [0]

/-- Whether `gemm` updates an unshared `C` in place. -/
def gemmInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (mat m m 3)
  BLASTest.addr (Mat.gemm 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmInPlace 8

-- A shared `C` is copied, and keeps its elements.
#guard
  let C := mat 4 4 3
  let D := Mat.gemm 1 (mat 4 4 1) (mat 4 4 2) 1 C
  C.toList == (mat 4 4 3).toList && D.toList == gemmModelList 1 (mat 4 4 1) (mat 4 4 2) 1 C

/-! ## `gemmNaive` -/

/-- Whether `gemm` computes the same matrix as `gemmNaive`, to the bit, for these shapes. -/
def gemmNaiveMatches (m n k : Nat) (α β : Float32) : Bool :=
  let A := mat m k 1
  let B := mat k n 2
  let C := mat m n 3
  let D := (Mat.gemm α A B β C).data
  let E := (Mat.gemmNaive α A B β C).data
  D.size == E.size && (List.range D.size).all fun i => D[i]! == E[i]!

#guard
  let A : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := Mat.ofPMat ⟨.ofList [5, 7, 6, 8], by decide⟩
  (Mat.gemmNaive 1 A B 0 (mat 2 2)).toList == [19, 43, 22, 50]

-- Odd shapes cover the last column, the leftover terms and the last row block of `gemm`.
#guard gemmNaiveMatches 5 4 3 1.5 0.5
#guard gemmNaiveMatches 1 1 1 2 3
#guard gemmNaiveMatches 17 9 13 (-0.25) 2
#guard gemmNaiveMatches 63 7 130 1 1
#guard gemmNaiveMatches 257 3 129 0.5 (-1)
#guard gemmNaiveMatches 300 5 260 1.25 0.75

-- Empty shapes.
#guard gemmNaiveMatches 0 3 2 1 1
#guard gemmNaiveMatches 3 0 2 1 1
#guard gemmNaiveMatches 3 2 0 1 2

/-- Whether `gemmNaive` updates an unshared `C` in place. -/
def gemmNaiveInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (mat m m 3)
  BLASTest.addr (Mat.gemmNaive 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmNaiveInPlace 8
#guard gemmNaiveInPlace 33

-- A shared `C` is copied, and keeps its elements.
#guard
  let C := mat 4 4 3
  let D := Mat.gemmNaive 1 (mat 4 4 1) (mat 4 4 2) 1 C
  C.toList == (mat 4 4 3).toList && D.toList == (Mat.gemm 1 (mat 4 4 1) (mat 4 4 2) 1 C).toList

/-! ## Matrices with an offset and a leading dimension -/

/--
The matrix `mat m n s` at the offset `off` with the leading dimension `ld`, in an array whose
other elements are `1e9 + 0.5`, a value that no test computes.
-/
def matLd (m n off ld : Nat) (s : Nat := 0) : Mat m n :=
  let a := ScalarArray.Float32Array.ofFn (n := off + ld * n) fun p =>
    let q := p.val - off
    if off ≤ p.val ∧ q % ld < m then ((q % ld * 7 + q / ld * 13 + s) % 11).toFloat32 - 5
    else 1e9 + 0.5
  (Mat.ofLd? a off ld).getD (mat m n s)

/-- The number of elements `1e9 + 0.5` in the array of `A`: those outside a matrix of `matLd`. -/
def outside (A : Mat m n) : Nat := A.data.toList.countP (· == 1e9 + 0.5)

#guard (matLd 3 4 5 7 1).toList == (mat 3 4 1).toList
#guard (matLd 3 4 5 7).data.size == 33
#guard outside (matLd 3 4 5 7) == 33 - 12
#guard ((Mat.ofLd? (m := 3) (n := 2) (.ofList [1, 2, 3, 4, 5]) 0 2).map Mat.toList).isNone
#guard ((Mat.ofLd? (m := 2) (n := 2) (.ofList [1, 2, 3, 4, 5]) 1 2).map Mat.toList) ==
  some [2, 3, 4, 5]

-- Rows and columns are vectors.
#guard ((matLd 3 4 5 7 1).col 2 (by decide)).toList == [(mat 3 4 1)[(0, 2)], (mat 3 4 1)[(1, 2)],
  (mat 3 4 1)[(2, 2)]]
#guard ((matLd 3 4 5 7 1).row 1 (by decide)).toList ==
  (List.range 4).map fun j => (mat 3 4 1).toList[1 + 3 * j]!

/-- Whether `gemm` and `gemmNaive` on matrices with offsets and leading dimensions compute the
same elements as on packed ones, and leave the rest of `C`'s array. -/
def gemmLdMatches (m n k : Nat) (α β : Float32) : Bool :=
  let A := matLd m k 3 (m + 2) 1
  let B := matLd k n 1 (k + 1) 2
  let C := matLd m n 4 (m + 3) 3
  let D := Mat.gemm α A B β C
  let E := Mat.gemmNaive α A B β C
  D.toList == gemmModelList α (mat m k 1) (mat k n 2) β (mat m n 3) &&
    E.toList == D.toList && outside D == outside C && outside E == outside C &&
    D.data.size == C.data.size

#guard gemmLdMatches 5 4 3 1.5 0.5
#guard gemmLdMatches 17 9 13 (-0.25) 2
#guard gemmLdMatches 257 3 129 0.5 (-1)
#guard gemmLdMatches 0 3 2 1 1
#guard gemmLdMatches 3 0 2 1 1
#guard gemmLdMatches 3 2 0 1 2

/-- Whether `gemm` updates the array of an unshared `C` with a leading dimension in place. -/
def gemmLdInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (matLd m m 2 (m + 1) 3)
  BLASTest.addr (Mat.gemm 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmLdInPlace 8

/-! ## `syrk` and `syrkT` -/

/-- Whether `(i, j)` is in the triangle `uplo`. -/
def inTri (uplo : Uplo) (i j : Nat) : Bool :=
  match uplo with
  | .upper => i ≤ j
  | .lower => j ≤ i

/-- The loops of the reference BLAS for `syrk`, with `trans = 'N'`, on an `Array`. -/
def syrkRef (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n) : List Float32 :=
  Id.run do
  let mut c := C.toList.toArray
  if n == 0 || ((α == 0 || k == 0) && β == 1) then return c.toList
  let rows (j : Nat) := (List.range n).filter (inTri uplo · j)
  if α == 0 then
    for j in List.range n do
      for i in rows j do
        c := c.set! (i + n * j) (if β == 0 then 0 else β * c[i + n * j]!)
    return c.toList
  for j in List.range n do
    if β == 0 then
      for i in rows j do c := c.set! (i + n * j) 0
    else if β != 1 then
      for i in rows j do c := c.set! (i + n * j) (β * c[i + n * j]!)
    for l in List.range k do
      let ajl := A[(j, l)]?.getD 0
      if ajl != 0 then
        let t := α * ajl
        for i in rows j do
          c := c.set! (i + n * j) (c[i + n * j]! + t * (A[(i, l)]?.getD 0))
  return c.toList

/-- The loops of the reference BLAS for `syrk`, with `trans = 'T'`, on an `Array`. -/
def syrkTRef (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32) (C : Mat n n) : List Float32 :=
  Id.run do
  let mut c := C.toList.toArray
  if n == 0 || ((α == 0 || k == 0) && β == 1) then return c.toList
  let rows (j : Nat) := (List.range n).filter (inTri uplo · j)
  if α == 0 then
    for j in List.range n do
      for i in rows j do
        c := c.set! (i + n * j) (if β == 0 then 0 else β * c[i + n * j]!)
    return c.toList
  for j in List.range n do
    for i in rows j do
      let mut t : Float32 := 0
      for l in List.range k do
        t := t + (A[(l, i)]?.getD 0) * (A[(l, j)]?.getD 0)
      c := c.set! (i + n * j) (if β == 0 then α * t else α * t + β * c[i + n * j]!)
  return c.toList

/--
Whether `syrk` and `syrkT` match the reference loops, on packed operands and on operands with
offsets and leading dimensions, and leave the rest of `C`'s array unchanged.
-/
def syrkMatches (n k : Nat) (uplo : Uplo) (α β : Float32) : Bool :=
  let ok₁ := (Mat.syrk uplo α (mat n k 1) β (mat n n 3)).toList ==
    syrkRef uplo α (mat n k 1) β (mat n n 3)
  let ok₂ := (Mat.syrkT uplo α (mat k n 1) β (mat n n 3)).toList ==
    syrkTRef uplo α (mat k n 1) β (mat n n 3)
  let C := matLd n n 4 (n + 3) 3
  let D := Mat.syrk uplo α (matLd n k 3 (n + 2) 1) β C
  let E := Mat.syrkT uplo α (matLd k n 1 (k + 1) 1) β C
  ok₁ && ok₂ && D.toList == syrkRef uplo α (mat n k 1) β (mat n n 3) &&
    E.toList == syrkTRef uplo α (mat k n 1) β (mat n n 3) &&
    outside D == outside C && outside E == outside C

#guard [Uplo.lower, .upper].all fun u =>
  syrkMatches 5 3 u 1.5 0.5 && syrkMatches 1 1 u 2 3 && syrkMatches 17 13 u (-0.25) 2 &&
    syrkMatches 40 7 u 1 1 && syrkMatches 5 3 u 0 0.5 && syrkMatches 5 3 u 1.5 0 &&
    syrkMatches 5 3 u 0 0 && syrkMatches 5 3 u 0 1 && syrkMatches 0 3 u 1 1 &&
    syrkMatches 3 0 u 1 1 && syrkMatches 3 0 u 2 0.5

-- `[[1, 2], [3, 4]] * [[1, 2], [3, 4]]ᵀ = [[5, 11], [11, 25]]`, on the lower triangle.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let C : Mat 2 2 := .ofPMat ⟨.ofList [0, 0, 7, 0], by decide⟩
  (Mat.syrk .lower 1 A 0 C).toList == [5, 11, 7, 25] &&
    (Mat.syrkT .upper 1 A 0 C).toList == [10, 0, 14, 20]

-- `syrk` skips the terms with `A[j, l] = 0`, so the infinity in `A[1, 0]` doesn't reach `C[1, 0]`.
#guard
  let A : Mat 2 1 := .ofPMat ⟨.ofList [0, 1 / 0], by decide⟩
  let C := Mat.syrk .lower 1 A 1 (mat 2 2 3)
  C[(1, 0)] == (mat 2 2 3)[(1, 0)] && C[(1, 1)] == 1 / 0

-- `syrkT` leaves `C` unchanged when `k = 0` and `β = 1`, even a `-0`.
#guard
  let C : Mat 1 1 := .ofFn fun _ _ => -0
  (Mat.syrkT .upper 2 (mat 0 1) 1 C)[(0, 0)].toBits == (-0 : Float32).toBits

-- `β = 0` sets the triangle to `0` without reading it, and `α = 0` doesn't read `A`.
#guard
  let nan : Float32 := 0 / 0
  let C : Mat 2 2 := .ofFn fun _ _ => nan
  let A : Mat 2 2 := .ofFn fun _ _ => nan
  (Mat.syrk .lower 0 A 0 C)[(1, 0)] == 0 && (Mat.syrkT .upper 0 A 0 C)[(0, 1)] == 0 &&
    (Mat.syrkT .upper 2 (mat 2 2) 0 C)[(0, 1)] ==
      (2 : Float32) * (Mat.syrkT .upper 1 (mat 2 2) 0 C)[(0, 1)]

/-- Whether `syrk` and `syrkT` update an unshared `C` in place. -/
def syrkInPlace (n : Nat) : Bool :=
  let (p, C) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, C') := withAddr (mat n n 3)
  BLASTest.addr (Mat.syrk .lower 1 (mat n 5 1) 1 C).data == p &&
    BLASTest.addr (Mat.syrkT .upper 1 (mat 5 n 1) 1 C').data == q

#guard syrkInPlace 8

/-! ## `trsm` and `trsmRight` -/

/-- A matrix with the elements of `mat n n s` in the triangle `uplo`, `n + 4 + i` on the diagonal,
and `other` elsewhere. -/
def triM (n : Nat) (s : Nat := 0) (other : Float32 := 0) (uplo : Uplo := .lower) : Mat n n :=
  .ofFn fun i j =>
    if i.val = j.val then (n + 4 + i.val).toFloat32
    else if inTri uplo i.val j.val then ((i.val * 7 + j.val * 13 + s) % 11).toFloat32 - 5
    else other

/-- The loops of the reference BLAS for `trsm`, with `side = 'L'` and `transa = 'N'`. -/
def trsmRef (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) : List Float32 :=
  Id.run do
  let mut b := B.toList.toArray
  if m == 0 || n == 0 then return b.toList
  if α == 0 then return b.toList.map fun _ => 0
  let a (i j : Nat) := A[(i, j)]?.getD 0
  for j in List.range n do
    for i in List.range m do b := b.set! (i + m * j) (α * b[i + m * j]!)
    match uplo with
    | .upper =>
      for k in (List.range m).reverse do
        if d == .nonUnit then b := b.set! (k + m * j) (b[k + m * j]! / a k k)
        for i in List.range k do
          b := b.set! (i + m * j) (b[i + m * j]! - b[k + m * j]! * a i k)
    | .lower =>
      for k in List.range m do
        if d == .nonUnit then b := b.set! (k + m * j) (b[k + m * j]! / a k k)
        for i in (List.range m).filter (k < ·) do
          b := b.set! (i + m * j) (b[i + m * j]! - b[k + m * j]! * a i k)
  return b.toList

/-- The loops of the reference BLAS for `trsm`, with `side = 'R'` and `transa = 'N'`. -/
def trsmRightRef (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    List Float32 := Id.run do
  let mut b := B.toList.toArray
  if m == 0 || n == 0 then return b.toList
  if α == 0 then return b.toList.map fun _ => 0
  let a (i j : Nat) := A[(i, j)]?.getD 0
  let cols := match uplo with
    | .upper => List.range n
    | .lower => (List.range n).reverse
  for j in cols do
    for i in List.range m do b := b.set! (i + m * j) (α * b[i + m * j]!)
    let ks := match uplo with
      | .upper => List.range j
      | .lower => (List.range n).filter (j < ·)
    for k in ks do
      for i in List.range m do
        b := b.set! (i + m * j) (b[i + m * j]! - a k j * b[i + m * k]!)
    if d == .nonUnit then
      for i in List.range m do b := b.set! (i + m * j) (b[i + m * j]! / a j j)
  return b.toList

/-- `A` with `NaN`s outside the triangle `uplo`, and on the diagonal when it is unit. -/
def withNaNs (uplo : Uplo) (d : Diag) (n : Nat) : Mat n n :=
  let nan : Float32 := 0 / 0
  let A := triM n 1 nan uplo
  match d with
  | .nonUnit => A
  | .unit => .ofFn fun i j => if i.val = j.val then nan else A[(i.val, j.val)]

/-- `A` at the offset `2` with the leading dimension `n + 3`, in an array of `1e9 + 0.5`. -/
def ldOf (A : Mat n n) : Mat n n :=
  (Mat.ofLd? (Mat.ofFn (m := n + 3) (n := n) fun i j =>
    if h : i.val < n then A[(i.val, j.val)]'⟨h, j.isLt⟩ else 1e9 + 0.5).data 0 (n + 3)).getD A

/--
Whether `trsm` and `trsmRight` match the reference loops, on packed operands and on operands with
offsets and leading dimensions, don't read the other triangle (nor the diagonal when it is unit),
and leave the rest of `B`'s array unchanged.
-/
def trsmMatches (m n : Nat) (uplo : Uplo) (d : Diag) (α : Float32) : Bool :=
  let A := triM m 1 0 uplo
  let A' := triM n 1 0 uplo
  let B := mat m n 2
  let B' := matLd m n 3 (m + 2) 2
  let X := Mat.trsm uplo d α (ldOf (withNaNs uplo d m)) B'
  let Y := Mat.trsmRight uplo d α (ldOf (withNaNs uplo d n)) B'
  (Mat.trsm uplo d α A B).toList == trsmRef uplo d α A B &&
    (Mat.trsmRight uplo d α A' B).toList == trsmRightRef uplo d α A' B &&
    X.toList == trsmRef uplo d α A B && Y.toList == trsmRightRef uplo d α A' B &&
    outside X == outside B' && outside Y == outside B'

#guard [Uplo.lower, .upper].all fun u => [Diag.unit, .nonUnit].all fun d =>
  trsmMatches 5 3 u d 1.5 && trsmMatches 1 1 u d 2 && trsmMatches 17 9 u d (-0.25) &&
    trsmMatches 40 33 u d 1 && trsmMatches 0 3 u d 1 && trsmMatches 3 0 u d 1 &&
    trsmMatches 5 3 u d 0

-- `α = 0` sets `B` to `0` without reading `A` or `B`.
#guard
  let nan : Float32 := 0 / 0
  let B : Mat 2 2 := .ofFn fun _ _ => nan
  let A : Mat 2 2 := .ofFn fun _ _ => nan
  (Mat.trsm .lower .nonUnit 0 A B).toList == [0, 0, 0, 0] &&
    (Mat.trsmRight .upper .unit 0 A B).toList == [0, 0, 0, 0]

/-- The residuals `A * X - α * B` and `X * A - α * B` of the solves, by `gemm`: zero up to
rounding. -/
def trsmResidual (n : Nat) (uplo : Uplo) : Float32 :=
  let A := triM n 1 0 uplo
  let B := mat n 4 2
  let X := Mat.trsm uplo .nonUnit 2 A B
  let Y := Mat.trsmRight uplo .nonUnit 2 (triM 4 1 0 uplo) B
  let r := Mat.gemm 1 A X (-2) B
  let s := Mat.gemm 1 Y (triM 4 1 0 uplo) (-2) B
  (r.toList ++ s.toList).foldl (fun s v => max s v.abs) 0

#guard trsmResidual 50 .lower < 1e-4 && trsmResidual 50 .upper < 1e-4

/-- Whether `trsm` and `trsmRight` update an unshared `B` in place. -/
def trsmInPlace (n : Nat) : Bool :=
  let (p, B) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, B') := withAddr (mat n n 3)
  let (r, B'') := withAddr (mat n n 4)
  let (s, B₃) := withAddr (mat n n 5)
  BLASTest.addr (Mat.trsm .lower .nonUnit 1 (triM n) B).data == p &&
    BLASTest.addr (Mat.trsm .upper .unit 2 (triM n 0 0 .upper) B₃).data == s &&
    BLASTest.addr (Mat.trsmRight .upper .unit 2 (triM n 0 0 .upper) B').data == q &&
    BLASTest.addr (Mat.trsmRight .lower .nonUnit 2 (triM n) B'').data == r

#guard trsmInPlace 8
