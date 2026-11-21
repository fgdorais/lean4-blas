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
Tests for the packed routines `spmv`, `tpmv`, `tpmvT`, `tpsv`, `tpsvT`, `spr` and `spr2` on
`Float32`, against transcriptions of the loops of the reference BLAS (`dspmv`, `dtpmv`, `dtpsv`,
`dspr` and `dspr2`), which walk the packed triangle with the index `KK` of the start of each column.
-/

open BLAS.Float32

namespace PackedTest

/--
The value of the elements outside the vectors of the tests, which no test computes.
-/
def mark : Float32 := 1e9 + 0.5

/-- The number of `mark`s in an array: the elements outside a vector of the tests. -/
def marks (a : ScalarArray.Float32Array) : Nat := a.toList.countP (· == mark)

/-- The bits of a list of floats. -/
def floatBits (l : List Float32) := l.map Float32.toBits

/-- `NaN`, for the unit diagonals, which the routines don't read. -/
def nan : Float32 := 0 / 0

/--
A vector of thirds of small integers computed from the indices and the seed `s`, so that the order
of the sums changes their roundings.
-/
def vec (n : Nat) (s : Nat := 0) : Vec n :=
  .ofFn fun i => (((i.val * 5 + s) % 9).toFloat32 - 4) / 3

/-- `vec n s` at the offset `off` with the stride `inc`, in an array of `mark`s. -/
def vecInc (n off inc : Nat) (s : Nat := 0) : Vec n :=
  let a := ScalarArray.Float32Array.ofFn (n := off + inc * n) fun p =>
    if off ≤ p.val ∧ (p.val - off) % inc = 0 then
      ((((p.val - off) / inc * 5 + s) % 9).toFloat32 - 4) / 3
    else mark
  (Vec.ofStride? a off inc).getD (vec n s)

/-- An element `i, j` of the tests' matrices: a third of a small integer. -/
def entry (i j s : Nat) : Float32 := (((i * 7 + j * 13 + s) % 11).toFloat32 - 5) / 3

/-- The diagonal of the triangular tests: far from zero, so that the solves are well conditioned. -/
def diagOf (n : Nat) (j : Nat) : Float32 := (n + 4 + j).toFloat32 / 3

/--
The triangle `uplo` of an `n × n` matrix packed by columns, with the diagonal `diag j` and the
other elements `entry i j s`.
-/
def packedVals (n : Nat) (uplo : Uplo) (diag : Nat → Float32) (s : Nat) : Array Float32 :=
  (List.range n).foldl (init := #[]) fun a j =>
    let rows := match uplo with
      | .upper => List.range (j + 1)
      | .lower => (List.range n).filter (j ≤ ·)
    rows.foldl (init := a) fun a i => a.push (if i = j then diag j else entry i j s)

/--
The packed triangle of `packedVals`, packed, and at the offset `1` with the stride `2`, in an array
of `mark`s.
-/
def apStore (n : Nat) (uplo : Uplo) (diag : Nat → Float32) (s : Nat := 0) :
    Vec (n * (n + 1) / 2) × Vec (n * (n + 1) / 2) :=
  let v := packedVals n uplo diag s
  let ap : Vec (n * (n + 1) / 2) := .ofFn fun p => v[p.val]!
  let a := ScalarArray.Float32Array.ofFn (n := 1 + 2 * (n * (n + 1) / 2)) fun q =>
    if 1 ≤ q.val ∧ (q.val - 1) % 2 = 0 then v[(q.val - 1) / 2]! else mark
  (ap, (Vec.ofStride? a 1 2).getD ap)

/-! ## The elements of the views -/

-- The upper triangle `[[1, 2, 4], [0, 3, 5], [0, 0, 6]]` is packed as `[1, 2, 3, 4, 5, 6]`, and
-- the lower triangle `[[1, 0, 0], [2, 4, 0], [3, 5, 6]]` as the same vector.
#guard
  let ap : Vec (3 * (3 + 1) / 2) := .ofList [1, 2, 3, 4, 5, 6]
  let els {T} [GetElem T (Nat × Nat) Float32 fun _ p => p.1 < 3 ∧ p.2 < 3] (t : T) :=
    (List.range 3).flatMap fun i => (List.range 3).map fun j => t[(i, j)]!
  els ap.upperPacked == [1, 2, 4, 0, 3, 5, 0, 0, 6] &&
    els ap.unitUpperPacked == [1, 2, 4, 0, 1, 5, 0, 0, 1] &&
    els ap.lowerPacked == [1, 0, 0, 2, 4, 0, 3, 5, 6] &&
    els ap.unitLowerPacked == [1, 0, 0, 2, 1, 0, 3, 5, 1] &&
    els ap.symUpperPacked == [1, 2, 4, 2, 3, 5, 4, 5, 6] &&
    els ap.symLowerPacked == [1, 2, 3, 2, 4, 5, 3, 5, 6]

/-! ## `tpmv` and `tpmvT` -/

-- `[[1, 2, 4], [0, 3, 5], [0, 0, 6]]` times `[1, 1, 1]` is `[7, 8, 6]`, and its transpose times
-- `[1, 1, 1]` is `[1, 5, 15]`.
#guard
  let ap : Vec (3 * (3 + 1) / 2) := .ofList [1, 2, 3, 4, 5, 6]
  let x : Vec 3 := .ofList [1, 1, 1]
  (Mat.tpmv .upper .nonUnit ap x).toList == [7, 8, 6] &&
    (Mat.tpmvT .upper .nonUnit ap x).toList == [1, 5, 15] &&
    (Mat.tpmv .lower .nonUnit ap x).toList == [1, 6, 14] &&
    (Mat.tpmvT .lower .nonUnit ap x).toList == [6, 9, 6]

/-- The loops of the reference BLAS for `tpmv`, or `tpmvT` if `t`, on an `Array`. -/
def tpmvRef (t : Bool) (uplo : Uplo) (d : Diag) (n : Nat) (ap x : List Float32) :
    List Float32 := Id.run do
  let a := ap.toArray
  let mut y := x.toArray
  let nonUnit := d == .nonUnit
  match t, uplo with
  | false, .upper =>
    let mut kk := 0
    for j in List.range n do
      let temp := y[j]!
      let mut k := kk
      for i in List.range j do
        y := y.set! i (y[i]! + temp * a[k]!)
        k := k + 1
      if nonUnit then y := y.set! j (y[j]! * a[kk + j]!)
      kk := kk + j + 1
  | false, .lower =>
    let mut kk := n * (n + 1) / 2 - 1
    for j in (List.range n).reverse do
      let temp := y[j]!
      let mut k := kk
      for i in ((List.range n).filter (j < ·)).reverse do
        y := y.set! i (y[i]! + temp * a[k]!)
        k := k - 1
      if nonUnit then y := y.set! j (y[j]! * a[kk + j + 1 - n]!)
      kk := kk - (n - j)
  | true, .upper =>
    let mut kk := n * (n + 1) / 2 - 1
    for j in (List.range n).reverse do
      let mut temp := y[j]!
      if nonUnit then temp := temp * a[kk]!
      let mut k := kk - 1
      for i in (List.range j).reverse do
        temp := temp + a[k]! * y[i]!
        k := k - 1
      y := y.set! j temp
      kk := kk - (j + 1)
  | true, .lower =>
    let mut kk := 0
    for j in List.range n do
      let mut temp := y[j]!
      if nonUnit then temp := temp * a[kk]!
      let mut k := kk + 1
      for i in (List.range n).filter (j < ·) do
        temp := temp + a[k]! * y[i]!
        k := k + 1
      y := y.set! j temp
      kk := kk + (n - j)
  return y.toList

/--
Whether `tpmv` (or `tpmvT` if `t`) matches the reference loops bit for bit, on packed operands and
on operands with offsets and strides, doesn't read the diagonal when it is unit (here `NaN`), and
leaves the rest of `x`'s array unchanged.
-/
def tpmvMatches (t : Bool) (n : Nat) (uplo : Uplo) (d : Diag) : Bool :=
  let f := if t then Mat.tpmvT uplo d else Mat.tpmv uplo d
  let (ap, ap') := apStore n uplo (fun j => if d == .unit then nan else diagOf n j) 1
  let r := tpmvRef t uplo d n ap.toList (vec n 2).toList
  let x := vecInc n 2 3 2
  let y := f ap' x
  floatBits (f ap (vec n 2)).toList == floatBits r && floatBits y.toList == floatBits r &&
    marks y.data == marks x.data

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d =>
    tpmvMatches t 5 u d && tpmvMatches t 1 u d && tpmvMatches t 0 u d && tpmvMatches t 40 u d

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d => tpmvMatches t 200 u d

/--
The address of the array of `x`, with `x`. It is not inlined, so the address is taken before `x`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (x : Vec n) : USize × Vec n := (BLASTest.addr x.data, x)

/-- Whether `tpmv`, `tpmvT`, `tpsv` and `tpsvT` update an unshared `x` in place. -/
def tpInPlace (n : Nat) : Bool :=
  let (lo, _) := apStore n .lower (diagOf n)
  let (up, _) := apStore n .upper (diagOf n)
  let (p, x) := withAddr (vecInc n 1 2)
  let (q, x') := withAddr (vecInc n 1 2 5)
  let (p', y) := withAddr (vecInc n 1 2 3)
  let (q', y') := withAddr (vecInc n 1 2 4)
  BLASTest.addr (Mat.tpmv .lower .nonUnit lo x).data == p &&
    BLASTest.addr (Mat.tpmvT .upper .unit up x').data == q &&
    BLASTest.addr (Mat.tpsv .upper .nonUnit up y).data == p' &&
    BLASTest.addr (Mat.tpsvT .lower .unit lo y').data == q'

#guard tpInPlace 8

/-! ## `tpsv` and `tpsvT` -/

-- `[[1, 2, 4], [0, 3, 5], [0, 0, 6]]` times `[1, 1, 1]` is `[7, 8, 6]`, and its transpose times
-- `[1, 1, 1]` is `[1, 5, 15]`.
#guard
  let ap : Vec (3 * (3 + 1) / 2) := .ofList [1, 2, 3, 4, 5, 6]
  (Mat.tpsv .upper .nonUnit ap (.ofList [7, 8, 6])).toList == [1, 1, 1] &&
    (Mat.tpsvT .upper .nonUnit ap (.ofList [1, 5, 15])).toList == [1, 1, 1] &&
    (Mat.tpsv .lower .nonUnit ap (.ofList [1, 6, 14])).toList == [1, 1, 1] &&
    (Mat.tpsvT .lower .nonUnit ap (.ofList [6, 9, 6])).toList == [1, 1, 1]

/-- The loops of the reference BLAS for `tpsv`, or `tpsvT` if `t`, on an `Array`. -/
def tpsvRef (t : Bool) (uplo : Uplo) (d : Diag) (n : Nat) (ap x : List Float32) :
    List Float32 := Id.run do
  let a := ap.toArray
  let mut y := x.toArray
  let nonUnit := d == .nonUnit
  match t, uplo with
  | false, .upper =>
    let mut kk := n * (n + 1) / 2 - 1
    for j in (List.range n).reverse do
      if nonUnit then y := y.set! j (y[j]! / a[kk]!)
      let temp := y[j]!
      let mut k := kk - 1
      for i in (List.range j).reverse do
        y := y.set! i (y[i]! - temp * a[k]!)
        k := k - 1
      kk := kk - (j + 1)
  | false, .lower =>
    let mut kk := 0
    for j in List.range n do
      if nonUnit then y := y.set! j (y[j]! / a[kk]!)
      let temp := y[j]!
      let mut k := kk + 1
      for i in (List.range n).filter (j < ·) do
        y := y.set! i (y[i]! - temp * a[k]!)
        k := k + 1
      kk := kk + (n - j)
  | true, .upper =>
    let mut kk := 0
    for j in List.range n do
      let mut temp := y[j]!
      let mut k := kk
      for i in List.range j do
        temp := temp - a[k]! * y[i]!
        k := k + 1
      if nonUnit then temp := temp / a[kk + j]!
      y := y.set! j temp
      kk := kk + j + 1
  | true, .lower =>
    let mut kk := n * (n + 1) / 2 - 1
    for j in (List.range n).reverse do
      let mut temp := y[j]!
      let mut k := kk
      for i in ((List.range n).filter (j < ·)).reverse do
        temp := temp - a[k]! * y[i]!
        k := k - 1
      if nonUnit then temp := temp / a[kk + j + 1 - n]!
      y := y.set! j temp
      kk := kk - (n - j)
  return y.toList

/--
Whether `tpsv` (or `tpsvT` if `t`) matches the reference loops bit for bit, on packed operands and
on operands with offsets and strides, doesn't read the diagonal when it is unit (here `NaN`), and
leaves the rest of `x`'s array unchanged.
-/
def tpsvMatches (t : Bool) (n : Nat) (uplo : Uplo) (d : Diag) : Bool :=
  let f := if t then Mat.tpsvT uplo d else Mat.tpsv uplo d
  let (ap, ap') := apStore n uplo (fun j => if d == .unit then nan else diagOf n j) 1
  let r := tpsvRef t uplo d n ap.toList (vec n 2).toList
  let x := vecInc n 2 3 2
  let y := f ap' x
  floatBits (f ap (vec n 2)).toList == floatBits r && floatBits y.toList == floatBits r &&
    marks y.data == marks x.data

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d =>
    tpsvMatches t 5 u d && tpsvMatches t 1 u d && tpsvMatches t 0 u d && tpsvMatches t 40 u d

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d => tpsvMatches t 200 u d

/-- `tpsv` undoes `tpmv`, and `tpsvT` undoes `tpmvT`, up to rounding. -/
def tpsvResidual (n : Nat) (uplo : Uplo) : Float32 :=
  let (ap, _) := apStore n uplo (diagOf n) 1
  let y := Mat.tpsv uplo .nonUnit ap (Mat.tpmv uplo .nonUnit ap (vec n 2))
  let z := Mat.tpsvT uplo .nonUnit ap (Mat.tpmvT uplo .nonUnit ap (vec n 2))
  ((y.toList ++ z.toList).zip ((vec n 2).toList ++ (vec n 2).toList)).foldl
    (fun s (u, v) => max s (u - v).abs) 0

#guard tpsvResidual 50 .lower < 1e-4 && tpsvResidual 50 .upper < 1e-4

-- The reference BLAS master doesn't skip a column whose element of the solution is zero, so an
-- infinity below it gives `NaN` (`0 * ∞`).
#guard
  let inf : Float32 := 1 / 0
  let ap : Vec (2 * (2 + 1) / 2) := .ofList [1, inf, 1]
  ((Mat.tpsv .lower .nonUnit ap (.ofList [0, 1])).toList.map Float32.isNaN) == [false, true] &&
    ((Mat.tpsvT .lower .nonUnit ap (.ofList [1, 0])).toList.map Float32.isNaN) == [true, false]

/-! ## `spmv` -/

-- The symmetric `[[1, 2, 4], [2, 3, 5], [4, 5, 6]]` times `[1, 1, 1]` is `[7, 10, 15]`.
#guard
  let ap : Vec (3 * (3 + 1) / 2) := .ofList [1, 2, 3, 4, 5, 6]
  let lp : Vec (3 * (3 + 1) / 2) := .ofList [1, 2, 4, 3, 5, 6]
  let x : Vec 3 := .ofList [1, 1, 1]
  (Mat.spmv .upper 1 ap x 0 x).toList == [7, 10, 15] &&
    (Mat.spmv .lower 1 lp x 0 x).toList == [7, 10, 15]

/-- The loops of the reference BLAS for `spmv`, on `Array`s. -/
def spmvRef (uplo : Uplo) (n : Nat) (α : Float32) (ap x : List Float32) (β : Float32)
    (y : List Float32) : List Float32 := Id.run do
  let a := ap.toArray
  let xs := x.toArray
  let mut b := y.toArray
  if n == 0 || (α == 0 && β == 1) then return b.toList
  if β != 1 then
    for i in List.range n do b := b.set! i (if β == 0 then 0 else β * b[i]!)
  if α == 0 then return b.toList
  let mut kk := 0
  for j in List.range n do
    let t₁ := α * xs[j]!
    let mut t₂ : Float32 := 0
    match uplo with
    | .upper =>
      let mut k := kk
      for i in List.range j do
        b := b.set! i (b[i]! + t₁ * a[k]!)
        t₂ := t₂ + a[k]! * xs[i]!
        k := k + 1
      b := b.set! j (b[j]! + t₁ * a[kk + j]! + α * t₂)
      kk := kk + j + 1
    | .lower =>
      b := b.set! j (b[j]! + t₁ * a[kk]!)
      let mut k := kk + 1
      for i in (List.range n).filter (j < ·) do
        b := b.set! i (b[i]! + t₁ * a[k]!)
        t₂ := t₂ + a[k]! * xs[i]!
        k := k + 1
      b := b.set! j (b[j]! + α * t₂)
      kk := kk + (n - j)
  return b.toList

/--
Whether `spmv` matches the reference loops bit for bit, on packed operands and on operands with
offsets and strides, and leaves the rest of `y`'s array unchanged.
-/
def spmvMatches (n : Nat) (uplo : Uplo) (α β : Float32) : Bool :=
  let (ap, ap') := apStore n uplo (diagOf n) 1
  let r := spmvRef uplo n α ap.toList (vec n 2).toList β (vec n 5).toList
  let y := vecInc n 1 2 5
  let z := Mat.spmv uplo α ap' (vecInc n 2 3 2) β y
  floatBits (Mat.spmv uplo α ap (vec n 2) β (vec n 5)).toList == floatBits r &&
    floatBits z.toList == floatBits r && marks z.data == marks y.data

#guard [Uplo.lower, .upper].all fun u =>
  spmvMatches 5 u 1.5 0.5 && spmvMatches 1 u 2 0 && spmvMatches 0 u 1 1 &&
    spmvMatches 40 u (-0.25) 1 && spmvMatches 17 u 0 0.5 && spmvMatches 17 u 0 0 &&
    spmvMatches 17 u 1 0

#guard spmvMatches 200 .upper (1 / 7) (-2) && spmvMatches 200 .lower (1 / 7) (-2)

/-- `spmv` agrees with `symv` on the full matrix of the view, up to rounding. -/
def spmvResidual (n : Nat) (uplo : Uplo) : Float32 :=
  let (ap, _) := apStore n uplo (diagOf n) 1
  let S : SymPacked uplo n := ⟨ap⟩
  let F : Mat n n := .ofFn fun i j => S[(i.val, j.val)]!
  ((Mat.spmv uplo 1.5 ap (vec n 2) 0.5 (vec n 5)).toList.zip
      (Mat.gemv 1.5 F (vec n 2) 0.5 (vec n 5)).toList).foldl
    (fun s (u, v) => max s (u - v).abs) 0

#guard spmvResidual 30 .lower < 1e-4 && spmvResidual 30 .upper < 1e-4

/-! ## `spr` and `spr2` -/

-- `[1, 2]` times its transpose, plus the upper `[[1, 2], [0, 3]]`, is `[[2, 4], [0, 7]]`.
#guard
  let ap : Vec (2 * (2 + 1) / 2) := .ofList [1, 2, 3]
  let x : Vec 2 := .ofList [1, 2]
  (Mat.spr .upper 1 x ap).toList == [2, 4, 7] && (Mat.spr .lower 1 x ap).toList == [2, 4, 7] &&
    (Mat.spr2 .upper 1 x x ap).toList == [3, 6, 11]

/-- The loops of the reference BLAS for `spr` (`y = none`) or `spr2`, on `Array`s. -/
def sprRef (uplo : Uplo) (n : Nat) (α : Float32) (x : List Float32) (y : Option (List Float32))
    (ap : List Float32) : List Float32 := Id.run do
  let xs := x.toArray
  let ys := (y.getD []).toArray
  let mut a := ap.toArray
  if n == 0 || α == 0 then return a.toList
  let mut kk := 0
  for j in List.range n do
    let rows := match uplo with
      | .upper => List.range (j + 1)
      | .lower => (List.range n).filter (j ≤ ·)
    match y with
    | none =>
      if xs[j]! != 0 then
        let temp := α * xs[j]!
        let mut k := kk
        for i in rows do
          a := a.set! k (a[k]! + xs[i]! * temp)
          k := k + 1
    | some _ =>
      if xs[j]! != 0 || ys[j]! != 0 then
        let t₁ := α * ys[j]!
        let t₂ := α * xs[j]!
        let mut k := kk
        for i in rows do
          a := a.set! k (a[k]! + xs[i]! * t₁ + ys[i]! * t₂)
          k := k + 1
    kk := kk + rows.length
  return a.toList

/-- A vector `vec n s` with zeros at the indices `3 * t + 1`, so that some columns are skipped. -/
def vecZ (n : Nat) (s : Nat) : Vec n :=
  .ofFn fun i => if i.val % 3 = 1 then 0 else (((i.val * 5 + s) % 9).toFloat32 - 4) / 3

/--
Whether `spr` and `spr2` match the reference loops bit for bit, on packed operands and on operands
with offsets and strides, and leave the rest of `ap`'s array unchanged.
-/
def sprMatches (n : Nat) (uplo : Uplo) (α : Float32) : Bool :=
  let (ap, ap') := apStore n uplo (diagOf n) 1
  let x := vecZ n 2
  let y := vecZ n 5
  let r := sprRef uplo n α x.toList none ap.toList
  let r2 := sprRef uplo n α x.toList (some y.toList) ap.toList
  let z := Mat.spr uplo α (vecInc n 2 3 2) ap'
  let z2 := Mat.spr2 uplo α (vecInc n 2 3 2) (vecInc n 1 2 5) ap'
  let r' := sprRef uplo n α (vec n 2).toList none ap.toList
  let r2' := sprRef uplo n α (vec n 2).toList (some (vec n 5).toList) ap.toList
  floatBits (Mat.spr uplo α x ap).toList == floatBits r &&
    floatBits (Mat.spr2 uplo α x y ap).toList == floatBits r2 &&
    floatBits z.toList == floatBits r' && marks z.data == marks ap'.data &&
    floatBits z2.toList == floatBits r2' && marks z2.data == marks ap'.data

#guard [Uplo.lower, .upper].all fun u =>
  sprMatches 5 u 1.5 && sprMatches 1 u 2 && sprMatches 0 u 1 && sprMatches 40 u (-0.25) &&
    sprMatches 17 u 0 && sprMatches 200 u (1 / 7)

-- The reference BLAS skips the columns `j` with `x[j] = 0` (with `x[j] = y[j] = 0` for `spr2`),
-- so an infinity elsewhere in `x` doesn't give them `NaN` (`∞ * 0`).
#guard
  let inf : Float32 := 1 / 0
  let ap : Vec (2 * (2 + 1) / 2) := .ofList [1, 2, 3]
  let x : Vec 2 := .ofList [inf, 0]
  let y : Vec 2 := .ofList [0, 0]
  ((Mat.spr .upper 1 x ap).toList.map Float32.isNaN) == [false, false, false] &&
    (Mat.spr .upper 1 x ap).toList.drop 1 == [2, 3] &&
    ((Mat.spr .lower 1 x ap).toList.map Float32.isNaN) == [false, true, false] &&
    (Mat.spr2 .upper 1 x y ap).toList.drop 1 == [2, 3]

/-- Whether `spr` and `spr2` update an unshared `ap` in place. -/
def sprInPlace (n : Nat) : Bool :=
  let (p, ap) := withAddr (apStore n .upper (diagOf n)).2
  let (q, lp) := withAddr (apStore n .lower (diagOf n) 3).2
  BLASTest.addr (Mat.spr .upper 1.5 (vec n 2) ap).data == p &&
    BLASTest.addr (Mat.spr2 .lower 1.5 (vec n 2) (vec n 5) lp).data == q

#guard sprInPlace 8

end PackedTest
