/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Level1

/-!
# Plane rotations

The Level 1 rotations of the reference BLAS: `rot` applies a plane rotation to two vectors, and
`rotm` a modified rotation, both by `zip`, a loop that updates the two arrays together, in place
when they are not shared. `rotg` and `rotmg` construct a rotation and a modified rotation from
scalars, step for step as the reference BLAS does.
-/

open ScalarArray Float64Array

namespace BLAS.Float64

/-! ## Two vectors at once -/

namespace Vec

variable {n : Nat}

/--
`zip f g x y` writes `f x[i] y[i]` over `x[i]` and `g x[i] y[i]` over `y[i]`, for each `i`, in
place when the arrays of `x` and `y` are not shared. Both values come from the old elements. It is
scalar-arrays' `zipModifyStride`, which checks each array once and then stores without checks.
-/
@[inline] public def zipData (f g : Float → Float → Float) (x y : Vec n) :
    Float64Array × Float64Array :=
  zipModifyStride x.data y.data x.stride y.stride n f g x.fits y.fits

public theorem zipData_eq (f g : Float → Float → Float) (x y : Vec n) :
    zipData f g x y = (x.data.modifyAt x.stride.idx 0 n (fun k u => f u y.data[y.stride.idx k]!),
      y.data.modifyAt y.stride.idx 0 n (fun k v => g x.data[x.stride.idx k]! v)) := by
  rw [zipData, zipModifyStride_eq, zipModifyAt_eq _ _ _ _
    (fun _ _ hi _ _ hj e => x.fits.idx_inj hi hj e) (fun _ _ hi _ _ hj e => y.fits.idx_inj hi hj e)]

/--
`zip f g x y`: the vectors `x` and `y` with `f x[i] y[i]` and `g x[i] y[i]` at `i`.

It takes `x` and `y` apart first, so that only their arrays go on to the loop and stay unshared.
-/
@[inline, expose] public def zip (f g : Float → Float → Float) : Vec n → Vec n → Vec n × Vec n
  | ⟨xd, xo, xi, xp, xb⟩, ⟨yd, yo, yi, yp, yb⟩ =>
    let d := zipData f g ⟨xd, xo, xi, xp, xb⟩ ⟨yd, yo, yi, yp, yb⟩
    have hd : d = _ := zipData_eq ..
    ({ data := d.1, off := xo, inc := xi, inc_pos := xp
       bound := by rw [hd, size_modifyAt]; exact xb },
     { data := d.2, off := yo, inc := yi, inc_pos := yp
       bound := by rw [hd, size_modifyAt]; exact yb })

@[simp] public theorem getElem_zip_fst (f g : Float → Float → Float) (x y : Vec n) (i : Nat)
    (h : i < n) : (zip f g x y).1[i] = f x[i] y[i] := by
  rw [getElem_of_data_eq_modifyAt (v := (zip f g x y).1) (w := x)
    (fun k u => f u y.data[y.stride.idx k]!)
    (by cases x; cases y; exact congrArg Prod.fst (zipData_eq ..)) (by cases x; cases y; rfl)
    (by cases x; cases y; rfl) i h, idx_stride,
    getElem!_pos y.data _ (y.index_lt h)]
  rfl

@[simp] public theorem getElem_zip_snd (f g : Float → Float → Float) (x y : Vec n) (i : Nat)
    (h : i < n) : (zip f g x y).2[i] = g x[i] y[i] := by
  rw [getElem_of_data_eq_modifyAt (v := (zip f g x y).2) (w := y)
    (fun k v => g x.data[x.stride.idx k]! v)
    (by cases x; cases y; exact congrArg Prod.snd (zipData_eq ..)) (by cases x; cases y; rfl)
    (by cases x; cases y; rfl) i h, idx_stride,
    getElem!_pos x.data _ (x.index_lt h)]
  rfl

/-! ## `rot` and `rotm` -/

/--
`rot c s x y` applies the plane rotation `[c s; -s c]` to the pairs `(x[i], y[i])`, as the
reference `drot`: `x[i] ↦ c * x[i] + s * y[i]` and `y[i] ↦ c * y[i] - s * x[i]`.
-/
@[expose] public def rot (c s : Float) (x y : Vec n) : Vec n × Vec n :=
  zip (fun u v => c * u + s * v) (fun u v => c * v - s * u) x y

@[simp] public theorem getElem_rot_fst (c s : Float) (x y : Vec n) (i : Nat) (h : i < n) :
    (rot c s x y).1[i] = c * x[i] + s * y[i] := getElem_zip_fst ..

@[simp] public theorem getElem_rot_snd (c s : Float) (x y : Vec n) (i : Nat) (h : i < n) :
    (rot c s x y).2[i] = c * y[i] - s * x[i] := getElem_zip_snd ..

end Vec

/--
The parameter of a modified rotation, the reference `DPARAM` array: `flag` is `DPARAM(1)` and
`h11`, `h21`, `h12`, `h22` are `DPARAM(2)` to `DPARAM(5)`, the entries of `H = [h11 h12; h21 h22]`.

The flag tells which entries `rotm` reads:
* `-2`: `H` is the identity and no entry is read;
* `-1`: all four entries are read;
* `0`: `h11 = h22 = 1` are implied, only `h21` and `h12` are read;
* any other value (`1` from `rotmg`, or NaN): `h21 = -1` and `h12 = 1` are implied, only `h11` and
  `h22` are read.
-/
public structure RotmParam where
  flag : Float
  h11 : Float
  h21 : Float
  h12 : Float
  h22 : Float
deriving Inhabited, Repr

namespace Vec

/--
`rotm p x y` applies the modified rotation `H` of `p` to the pairs `(x[i], y[i])`, as the reference
`drotm`: `x[i] ↦ x[i] * h11 + y[i] * h12` and `y[i] ↦ x[i] * h21 + y[i] * h22`, with the entries
implied by the flag written out in the reference's way (see `RotmParam`).
-/
@[expose] public def rotm (p : RotmParam) (x y : Vec n) : Vec n × Vec n :=
  if p.flag + 2 == 0 then (x, y)
  else if p.flag < 0 then
    zip (fun w z => w * p.h11 + z * p.h12) (fun w z => w * p.h21 + z * p.h22) x y
  else if p.flag == 0 then
    zip (fun w z => w + z * p.h12) (fun w z => w * p.h21 + z) x y
  else
    zip (fun w z => w * p.h11 + z) (fun w z => -w + p.h22 * z) x y

@[simp] public theorem getElem_rotm_fst (p : RotmParam) (x y : Vec n) (i : Nat) (h : i < n) :
    (rotm p x y).1[i] =
      if p.flag + 2 == 0 then x[i]
      else if p.flag < 0 then x[i] * p.h11 + y[i] * p.h12
      else if p.flag == 0 then x[i] + y[i] * p.h12
      else x[i] * p.h11 + y[i] := by
  unfold rotm; split <;> (try split) <;> (try split) <;> simp [*]

@[simp] public theorem getElem_rotm_snd (p : RotmParam) (x y : Vec n) (i : Nat) (h : i < n) :
    (rotm p x y).2[i] =
      if p.flag + 2 == 0 then y[i]
      else if p.flag < 0 then x[i] * p.h21 + y[i] * p.h22
      else if p.flag == 0 then x[i] * p.h21 + y[i]
      else -x[i] + p.h22 * y[i] := by
  unfold rotm; split <;> (try split) <;> (try split) <;> simp [*]

end Vec

/-! ## `rotg` -/

/-- The result of `rotg a b`: the rotation `c`, `s`, the rotated `r`, and the reconstruction
value `z` that the reference `drotg` returns in `b`. -/
public structure Rotg where
  r : Float
  z : Float
  c : Float
  s : Float
deriving Inhabited, Repr

namespace Rotg

/-- The smallest normal number `2⁻¹⁰²²`, the reference `safmin`. -/
@[expose] public def safmin : Float := Float.ofBits 0x0010000000000000

/-- `2¹⁰²³`, the reference `safmax`. -/
@[expose] public def safmax : Float := Float.ofBits 0x7FE0000000000000

/-- Fortran's `sign(1, x)`: `-1` when the sign bit of `x` is set, `1` otherwise. -/
@[inline, expose] public def sign1 (x : Float) : Float :=
  if x.toBits >>> 63 == 0 then 1 else -1

/--
Fortran's `max` of two values as gfortran compiles it: the first unless the second is greater.
-/
@[inline, expose] public def fmax (a b : Float) : Float := if b > a then b else a

/--
Fortran's `min` of two values as gfortran compiles it: the first unless the second is smaller.
-/
@[inline, expose] public def fmin (a b : Float) : Float := if b < a then b else a

end Rotg

open Rotg in
/--
`rotg a b` constructs the plane rotation that zeros `b`, step for step as the reference `drotg`
(the Anderson 2017 version): `c * a + s * b = r` and `-s * a + c * b = 0`, with `r` carrying the
sign of the larger of `a` and `b` in magnitude, computed with scaling so that it does not overflow
or underflow when the result is representable.
-/
@[expose] public def rotg (a b : Float) : Rotg :=
  let anorm := a.abs
  let bnorm := b.abs
  if bnorm == 0 then { r := a, z := 0, c := 1, s := 0 }
  else if anorm == 0 then { r := b, z := 1, c := 0, s := 1 }
  else
    let scl := fmin safmax (fmax (fmax safmin anorm) bnorm)
    let sigma := if anorm > bnorm then sign1 a else sign1 b
    let r := sigma * (scl * ((a / scl) * (a / scl) + (b / scl) * (b / scl)).sqrt)
    let c := a / r
    let s := b / r
    let z := if anorm > bnorm then s else if c != 0 then 1 / c else 1
    { r, z, c, s }

/-! ## `rotmg` -/

namespace Rotmg

/-- The reference's rescaling factor `GAM`. -/
@[expose] public def gam : Float := 4096

/-- The reference's `GAMSQ`, the literal `16777216.D0`, which is `gam * gam`. -/
@[expose] public def gamsq : Float := 16777216

/--
The reference's `RGAMSQ`, the literal `5.9604645D-8` (close to, but not exactly, `1 / gamsq`).
-/
@[expose] public def rgamsq : Float := 5.9604645e-8

/-- The state of `rotmg`: the flag, `H`, and the scaled `d1`, `d2`, `x1`. -/
public structure State where
  flag : Float
  h11 : Float
  h21 : Float
  h12 : Float
  h22 : Float
  d1 : Float
  d2 : Float
  x1 : Float

/--
The reference's reset when the rotation does not exist: flag `-1`, `H = 0`, `d1 = d2 = x1 = 0`.
-/
@[expose] public def State.zero : State :=
  { flag := -1, h11 := 0, h21 := 0, h12 := 0, h22 := 0, d1 := 0, d2 := 0, x1 := 0 }

/-- Before a rescaling step, the reference writes out the entries implied by flags `0` and `1` and
sets the flag to `-1`. -/
@[expose] public def State.expand (t : State) : State :=
  if t.flag == 0 then { t with h11 := 1, h22 := 1, flag := -1 }
  else if t.flag == 1 then { t with h21 := -1, h12 := 1, flag := -1 }
  else t

/-- The reference's `DO WHILE` loop that brings `d1` into `(rgamsq, gamsq)`, with fuel: a finite
nonzero `d1` takes at most 46 steps, while for an infinite `d1` the reference loops forever and
this stops when the fuel runs out. -/
@[expose] public def scale1 : Nat → State → State
  | 0, t => t
  | fuel + 1, t =>
    if t.d1 ≤ rgamsq || t.d1 ≥ gamsq then
      let t := t.expand
      if t.d1 ≤ rgamsq then
        scale1 fuel
          { t with d1 := t.d1 * (gam * gam), x1 := t.x1 / gam, h11 := t.h11 / gam,
                   h12 := t.h12 / gam }
      else
        scale1 fuel
          { t with d1 := t.d1 / (gam * gam), x1 := t.x1 * gam, h11 := t.h11 * gam,
                   h12 := t.h12 * gam }
    else t

/-- The reference's `DO WHILE` loop that brings `|d2|` into `(rgamsq, gamsq)`, with fuel as in
`scale1`. -/
@[expose] public def scale2 : Nat → State → State
  | 0, t => t
  | fuel + 1, t =>
    if t.d2.abs ≤ rgamsq || t.d2.abs ≥ gamsq then
      let t := t.expand
      if t.d2.abs ≤ rgamsq then
        scale2 fuel { t with d2 := t.d2 * (gam * gam), h21 := t.h21 / gam, h22 := t.h22 / gam }
      else
        scale2 fuel { t with d2 := t.d2 / (gam * gam), h21 := t.h21 * gam, h22 := t.h22 * gam }
    else t

/-- The fuel of `scale1` and `scale2`. -/
@[expose] public def fuel : Nat := 128

end Rotmg

/-- The result of `rotmg d1 d2 x1 y1`: the parameter of the modified rotation and the new `d1`,
`d2`, `x1`, which the reference `drotmg` returns in its arguments. -/
public structure Rotmg where
  param : RotmParam
  d1 : Float
  d2 : Float
  x1 : Float
deriving Inhabited, Repr

open Rotmg in
/--
`rotmg d1 d2 x1 y1` constructs the modified rotation `H` that zeros the second component of
`(√d1 * x1, √d2 * y1)`, step for step as the reference `drotmg`.

The reference writes only the entries of `DPARAM` that the flag says `rotm` reads, and leaves the
others as they were; here those entries hold the values the flag implies (`H` is the identity for
flag `-2`). The reference also leaves `DH11` and `DH22` unset on the flag `0` path, and `DH21` and
`DH12` on the flag `1` path, until a rescaling writes them; those are not read either. Where the
reference loops forever on an infinite `d1` or `d2`, this stops after `Rotmg.fuel` steps.
-/
@[expose] public def rotmg (d1 d2 x1 y1 : Float) : Rotmg :=
  let finish (t : State) : Rotmg :=
    let t := if t.d1 != 0 then scale1 fuel t else t
    let t := if t.d2 != 0 then scale2 fuel t else t
    let param : RotmParam :=
      if t.flag < 0 then
        { flag := t.flag, h11 := t.h11, h21 := t.h21, h12 := t.h12, h22 := t.h22 }
      else if t.flag == 0 then
        { flag := t.flag, h11 := 1, h21 := t.h21, h12 := t.h12, h22 := 1 }
      else
        { flag := t.flag, h11 := t.h11, h21 := -1, h12 := 1, h22 := t.h22 }
    { param, d1 := t.d1, d2 := t.d2, x1 := t.x1 }
  if d1 < 0 then
    { param := { flag := -1, h11 := 0, h21 := 0, h12 := 0, h22 := 0 }, d1 := 0, d2 := 0, x1 := 0 }
  else
    let p2 := d2 * y1
    if p2 == 0 then
      { param := { flag := -2, h11 := 1, h21 := 0, h12 := 0, h22 := 1 }, d1, d2, x1 }
    else
      let p1 := d1 * x1
      let q2 := p2 * y1
      let q1 := p1 * x1
      if q1.abs > q2.abs then
        let h21 := -y1 / x1
        let h12 := p2 / p1
        let u := 1 - h12 * h21
        if u > 0 then
          finish
            { flag := 0, h11 := 1, h21, h12, h22 := 1, d1 := d1 / u, d2 := d2 / u,
              x1 := x1 * u }
        else finish State.zero
      else if q2 < 0 then finish State.zero
      else
        let h11 := p1 / p2
        let h22 := x1 / y1
        let u := 1 + h11 * h22
        finish
          { flag := 1, h11, h21 := -1, h12 := 1, h22, d1 := d2 / u, d2 := d1 / u,
            x1 := y1 * u }

end BLAS.Float64
