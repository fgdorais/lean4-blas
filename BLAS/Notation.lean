/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Term
public import BLAS.Ops

/-!
# The `blas%` notation

The root module `BLAS` doesn't import this one, because it makes `blas%` a keyword. Outside of
`blas%` it adds nothing else: the right side of an update is in its own syntax category, so `ᵀ` and
`A[:, j]` mean something only there, and `•` and `*` have the precedence of the formula.

`blas% y := e` updates `y` by a single routine, chosen from the form of `e` and the kinds of its
operands. `y += e` is `y := y + e`, and `y -= e` is `y := y - e`. A block of updates, one per
line, needs `blas%` only once:

```
blas% do
  y := α • A * x + β • y
  y -= 2 • A[:, 0]
  x := A.lower⁻¹ * x
```

In a `do` block, `blas% do …` reassigns the mutable variables that are its targets, in order, and
`blas% y := e` is a block of one statement. As a term, `blas% do …` is the new value of the last
target, and `blas%(y := e)`, a block of one statement, is the routine call itself. A block is the
only `do` of its expression: its statements can't contain a `do` block or another `blas%`.

| Update                    | Expansion                | Routine                   |
|---------------------------|--------------------------|---------------------------|
| `y := α • A * x + β • y`  | `MulAdd.run α A x β y`   | `gemv`, `gemm`, `symv`, … |
| `y := α • A * x + y`      | `MulAcc.run α A x y`     | the same, and `ger`       |
| `y := α • x + y`          | `Axpy.run α x y`         | `axpy`                    |
| `y := α • x + β • y`      | `Axpby.run α x β y`      | `axpby`                   |
| `y := α • x`              | `Axpby.run α x 0 y`      | `axpby`                   |
| `x := α • x`              | `Scal.run α x`           | `scal`                    |
| `y := x`                  | `Copy.run x y`           | `copy`                    |
| `x := T⁻¹ * x`            | `Solve.run T x`          | `trsv`, `trsm`, …         |
| `B := α • T⁻¹ * B`        | `ScaledSolve.run α T B`  | `trsm`, `trsmT`           |
| `B := α • B * T⁻¹`        | `SolveRight.run α B T`   | `trsmRight`, `trsmRightT` |
| `x := T * x`              | `MulIn.run T x`          | `trmv`, `trmm`, …         |
| `B := α • T * B`          | `ScaledMulIn.run α T B`  | `trmm`, `trmmT`           |
| `B := α • B * T`          | `MulInRight.run α B T`   | `trmmRight`, `trmmRightT` |

The routine follows from the kinds of the operands. For `MulAdd`, a matrix and a vector is `gemv`,
a transpose `Aᵀ` and a vector `gemvT`, two matrices `gemm`, and transposes `gemmTN` (`Aᵀ * B`),
`gemmNT` (`A * Bᵀ`) and `gemmTT` (`Aᵀ * Bᵀ`); a symmetric view `A.symLower` is `symv`, `symm` or
`symmRight`, and a triangle target `C.lower` is `gemmtr`, `gemmtrTN`, `gemmtrNT` or `gemmtrTT`. A
triangle `T` is a view such as `A.lower` or `A.unitUpper`, or its transpose `A.lowerᵀ`, and its
inverse is `A.lower⁻¹` or `A.lowerᵀ⁻¹`. The band views select the band routines: `A.band m kl ku`
and its transpose are `gbmv` and `gbmvT`, `A.symUpperBand` and `A.symLowerBand` are `sbmv`, and a
triangular band `A.upperBand`, `A.unitLowerBand`, … is `tbmv` or `tbsv`, or `tbmvT` or `tbsvT` for
its transpose (`BLAS.Float64.BandView`). The packed views of a vector `ap` select the packed
routines: `ap.symUpperPacked` and `ap.symLowerPacked` are `spmv`, and `spr` or `spr2` as a target,
and a packed triangle `ap.upperPacked`, `ap.unitLowerPacked`, … is `tpmv` or `tpsv`, or `tpmvT` or
`tpsvT` for its transpose (`BLAS.Float64.PackedView`). A missing `α` is `1`, a missing `β • y`
is `β = 0`, which sets `y` to `0` without reading it, as in the reference BLAS, and a bare `y` is
`β = 1`. The summands may come in any order, and a subtracted summand `- α • …` has the scalar `-α`
(`-1` if it has none). Floating-point negation is exact, and `a - b` is `a + (-b)`, so
`y := A * x - y` is `gemv 1 A x (-1) y` and `y -= α • x` is `axpy (-α) x y`, to the bit.

A product over one of its operands, `x := T * x`, is a triangular product in place: `trmv` and
`trmm` have no `β`, and `trmv` no `α`. For a general matrix, `x := A * x` is an error, as `gemv`
and `gemm` don't update an operand; write `y := A * x` to a separate `y`.

### Triangle targets

A target `C.lower` or `C.upper` is the triangle of the square matrix `C` that the routine updates,
which leaves the other triangle of `C` as it is: `syr`, `syr2`, `syrk`, `syr2k` and `gemmtr`. The
statement reassigns `C`. A rank-k update `A * Aᵀ` or `Aᵀ * A`, of a single variable `A`, is `syrk`
or `syrkT`, or `syr` for a vector, and a rank-2k update `A * Bᵀ + B * Aᵀ` or `Aᵀ * B + Bᵀ * A`,
with the same scalar on both summands, is `syr2k` or `syr2kT`, or `syr2` for vectors. Any other
product over a triangle is `gemmtr`.

| Update                                              | Expansion                     |
|-----------------------------------------------------|-------------------------------|
| `C.lower := α • A * Aᵀ + β • C.lower`               | `RankK.run α A β C.lower`     |
| `C.lower += α • x * xᵀ`                             | `RankKAcc.run α x C.lower`    |
| `C.lower := α • A * Bᵀ + α • B * Aᵀ + β • C.lower`  | `Rank2K.run α A B β C.lower`  |
| `C.lower += α • x * yᵀ + α • y * xᵀ`                | `Rank2KAcc.run α x y C.lower` |
| `C.lower := α • A * B + β • C.lower`                | `MulAdd.run α A B β C.lower`  |

`RankKAcc` and `Rank2KAcc` are `RankK` and `Rank2K` with `β = 1` for matrices, and `syr` and
`syr2`, which have no `β`, for vectors.

## Grammar

The right side is a sum of summands `s • f * g`, which may be subtracted, as in `- f + g - h`,
with an optional scalar `s` and one or two factors `f` and `g`. The `•` ends the scalar, so the
scalar is a product or quotient of terms, as in `2 * a • A * x` or `-α / 2 • x`, with no
parentheses: only a scalar sum or difference needs them, `(a - b) • x`, as `+` and `-` separate the
summands. A scalar term and a factor are Lean terms above the
precedence of `*`, such as `α`, `-α`, `f a`, `x.dot y` or `A.lower⁻¹`. A factor can also be a
transpose `Aᵀ` or the inverse `Aᵀ⁻¹` of one, with no copy, or a column `A[:, j]` or a row
`A[i, :]` of a matrix `A`, as a vector with no copy.

An update that no single routine computes is an error at compile time, never a combination of
routines: `A * B * x` (two products), `y := A * x + z` with `z` not the target, or a product of
operands of sizes or kinds that no routine takes (no instance of the class), such as
`A := x * yᵀ`, as `ger` has no `β`. So the expansion is always one call, with the speed and the
specification of its routine.
-/

namespace BLAS.Notation

open Lean

/-- A factor of a summand of a `blas%` update: a matrix, a vector, or a view of one. -/
declare_syntax_cat blasFactor

/-- A factor is a term above the precedence of `*`, such as `A`, `A.lower⁻¹` or `f x`. -/
syntax term:75 : blasFactor

/-- `Aᵀ` is the transpose of `A`, with no copy. -/
syntax (name := blasTranspose) term:max noWs "ᵀ" : blasFactor

/-- `Aᵀ⁻¹` is the inverse of the transpose of `A`, a triangular view, with no copy. -/
syntax (name := blasTransposeInv) term:max noWs "ᵀ" noWs "⁻¹" : blasFactor

/-- `A[:, j]` is column `j` of the matrix `A`, as a vector, with no copy. -/
syntax ident noWs "[" ":" ", " term "]" : blasFactor

/-- `A[i, :]` is row `i` of the matrix `A`, as a vector, with no copy. -/
syntax ident noWs "[" term ", " ":" "]" : blasFactor

/-- A scalar of a summand of a `blas%` update. -/
declare_syntax_cat blasScalar

/-- A scalar is a product or quotient of terms above the precedence of `*`. -/
syntax term:75 ((" * " <|> " / ") term:75)* : blasScalar

/-- A summand of a `blas%` update. -/
declare_syntax_cat blasSummand

/-- A summand `s • f * g`, with an optional scalar `s` and one or more factors. -/
syntax (atomic(blasScalar " • "))? blasFactor (" * " blasFactor)* : blasSummand

/-- The right side of a `blas%` update. -/
declare_syntax_cat blasSum

/-- The right side of a `blas%` update is a sum and difference of summands. -/
syntax ("-")? blasSummand ((" + " <|> " - ") blasSummand)* : blasSum

/-- A summand of the right side of a `blas%` update, with its optional scalar. -/
private inductive Summand where
  /-- `α • a * x`, with the factors `fa` and `fx` as written. -/
  | prod (c : Option Term) (a x : Term) (fa fx : TSyntax `blasFactor)
  /-- `α • x`. -/
  | plain (c : Option Term) (x : Term)
  deriving Inhabited

/-- The arithmetic that a parenthesized factor can't be, as no single routine computes it. -/
private meta def opKinds : List SyntaxNodeKind :=
  [``«term_-_», ``«term_/_», ``«term_+_», ``«term_*_», ``«term_•_»]

/-- Removes the parentheses around a term. -/
private meta partial def unparen : Term → Term
  | `(($t)) => unparen t
  | t => t

/-- The term of a scalar. -/
private meta def scalar (s : TSyntax `blasScalar) : MacroM Term := do
  let mut acc : Term := ⟨s.raw[0]⟩
  for p in s.raw[1].getArgs do
    let a : Term := ⟨p[1]⟩
    acc ← if (p[0].find? (·.isToken "/")).isSome then `($acc / $a) else `($acc * $a)
  return acc

/-- The term of a factor. -/
private meta def factor (f : TSyntax `blasFactor) : MacroM Term := do
  if f.raw.isOfKind ``blasTranspose then return ← `(BLAS.Transpose.mk $(⟨f.raw[0]⟩))
  if f.raw.isOfKind ``blasTransposeInv then return ← `((BLAS.Transpose.mk $(⟨f.raw[0]⟩))⁻¹)
  match f with
  | `(blasFactor| $A:ident[:, $j]) => `(($A).col $j (by get_elem_tactic))
  | `(blasFactor| $A:ident[$i, :]) => `(($A).row $i (by get_elem_tactic))
  | `(blasFactor| $t:term) =>
    let t := unparen t
    if opKinds.contains t.raw.getKind then
      Macro.throwErrorAt t "blas%: no single BLAS routine computes this factor; \
        write it with a separate update first"
    return t
  | _ => Macro.throwUnsupported

/--
Classifies a summand of the right side of a `blas%` update, negated if `neg`: its scalar `α`
becomes `-α`, and a missing one `-1`. Negation is exact, so `y - α • x` is `y + (-α) • x` to the
bit.
-/
private meta def classify (s : TSyntax `blasSummand) (neg : Bool) : MacroM Summand := do
  match s with
  | `(blasSummand| $[$c:blasScalar •]? $f:blasFactor $[* $gs:blasFactor]*) =>
    let c ← c.mapM scalar
    let c ← if neg then some <$> (match c with | some c => `(-$c) | none => `(-1)) else pure c
    match gs with
    | #[] => return .plain c (← factor f)
    | #[g] => return .prod c (← factor f) (← factor g) f g
    | _ => Macro.throwErrorAt s "blas%: no single BLAS routine computes a product of three \
        factors"
  | _ => Macro.throwUnsupported

/-- Whether `t` is the target `y` of the update. -/
private meta def isTarget (y : Ident) (t : Term) : Bool :=
  t.raw.isIdent && t.raw.getId == y.getId

/-- The variable `A` of a factor `A`, if it is one. -/
private meta def factorVar? (f : TSyntax `blasFactor) : Option Name :=
  if f.raw.getNumArgs == 1 && f.raw[0].isIdent then some f.raw[0].getId else none

/-- The variable `A` of a factor `Aᵀ`, if it is one. -/
private meta def transposeVar? (f : TSyntax `blasFactor) : Option Name :=
  if f.raw.isOfKind ``blasTranspose && f.raw[0].isIdent then some f.raw[0].getId else none

/--
The variables `A` and `B` of the factors of `A * Bᵀ`, as `(true, A, B)`, or of `Aᵀ * B`, as
`(false, A, B)`.
-/
private meta def outerVars? (f g : TSyntax `blasFactor) : Option (Bool × Name × Name) :=
  match factorVar? f, transposeVar? g, transposeVar? f, factorVar? g with
  | some a, some b, _, _ => some (true, a, b)
  | _, _, some a, some b => some (false, a, b)
  | _, _, _, _ => none

/-- Whether the scalars `c` and `d` are the same, as written. -/
private meta def sameScalar : Option Term → Option Term → Bool
  | none, none => true
  | some c, some d => c.raw.structEq d.raw
  | _, _ => false

/--
Whether the target `y` is the triangle `C.lower` or `C.upper` of a matrix `C`, which only the
routines `syr`, `syr2`, `syrk`, `syr2k` and `gemmtr` update.
-/
private meta def isView (y : Ident) : Bool :=
  match y.getId with
  | .str (.str _ _) _ => true
  | _ => false

/-- The summands of the right side of a `blas%` update, with whether each one is subtracted. -/
private meta def summands (e : TSyntax `blasSum) : Array (Bool × TSyntax `blasSummand) := Id.run do
  let mut out := #[(!e.raw[0].isNone, ⟨e.raw[1]⟩)]
  for p in e.raw[2].getArgs do
    out := out.push ((p[0].find? (·.isToken "-")).isSome, ⟨p[1]⟩)
  return out

/--
The routine call of the update `y := e`, and of `y += e` if `add`, or `y -= e` if also `sub`.
-/
private meta def expand (y : Ident) (e : TSyntax `blasSum) (add sub : Bool) : MacroM Term := do
  let mut target : Option (Option Term) := if add then some none else none
  let mut others : Array Summand := #[]
  for (neg, t) in summands e do
    let s ← classify t (neg != sub)
    match s with
    | .plain c x =>
      if isTarget y x then
        if target.isSome then
          Macro.throwErrorAt t s!"blas%: `{y.getId}` occurs twice; combine its scalars"
        target := some c
      else others := others.push s
    | .prod .. => others := others.push s
  let fail {α} : MacroM α := Macro.throwErrorAt e
    s!"blas%: no single BLAS routine computes this update of `{y.getId}`"
  match others, target with
  -- `C.lower := α • A * Bᵀ + α • B * Aᵀ + β • C.lower`, and `Aᵀ * B + Bᵀ * A`.
  | #[.prod c a _ fa fx, .prod c' b _ fb fy], tgt =>
    let some (n, a₁, b₁) := outerVars? fa fx | fail
    let some (n', b₂, a₂) := outerVars? fb fy | fail
    unless isView y && n == n' && a₁ == a₂ && b₁ == b₂ && sameScalar c c' do fail
    let α ← c.getDM `(1)
    match tgt with
    | none => `(BLAS.Rank2K.run $α $a $b 0 $y)
    | some none => `(BLAS.Rank2KAcc.run $α $a $b $y)
    | some (some β) => `(BLAS.Rank2K.run $α $a $b $β $y)
  -- `y := α • A * x + β • y`, the solves, and the triangular products.
  | #[.prod c a x fa fx], tgt =>
    match unparen a, unparen x with
    | `($t⁻¹), x =>
      unless isTarget y x && tgt.isNone do fail
      match c with
      | none => `(BLAS.Solve.run $t $y)
      | some c => `(BLAS.ScaledSolve.run $c $t $y)
    | b, `($t⁻¹) =>
      unless isTarget y b && tgt.isNone do fail
      `(BLAS.SolveRight.run $(c.getD (← `(1))) $y $t)
    | a, x =>
      let α ← c.getDM `(1)
      -- `C.lower := α • A * Aᵀ + β • C.lower`, and `Aᵀ * A`.
      if let some (_, a₁, b₁) := outerVars? fa fx then
        if isView y && a₁ == b₁ then
          return ← match tgt with
            | none => `(BLAS.RankK.run $α $a 0 $y)
            | some none => `(BLAS.RankKAcc.run $α $a $y)
            | some (some β) => `(BLAS.RankK.run $α $a $β $y)
      match tgt with
      | none =>
        if isTarget y x then
          match c with
          | none => `(BLAS.MulIn.run $a $y)
          | some c => `(BLAS.ScaledMulIn.run $c $a $y)
        else if isTarget y a then `(BLAS.MulInRight.run $α $y $x)
        else `(BLAS.MulAdd.run $α $a $x 0 $y)
      | some none => `(BLAS.MulAcc.run $α $a $x $y)
      | some (some β) => `(BLAS.MulAdd.run $α $a $x $β $y)
  -- `y := α • x + y`.
  | #[.plain c x], some none => `(BLAS.Axpy.run $(← c.getDM `(1)) $x $y)
  -- `y := α • x + β • y`.
  | #[.plain c x], some (some β) => `(BLAS.Axpby.run $(← c.getDM `(1)) $x $β $y)
  -- `y := α • x`, which sets `y` to `α * x` without reading it.
  | #[.plain (some c) x], none => `(BLAS.Axpby.run $c $x 0 $y)
  -- `y := x`.
  | #[.plain none x], none => `(BLAS.Copy.run $x $y)
  -- `x := α • x`.
  | #[], some (some c) => `(BLAS.Scal.run $c $y)
  | _, _ => fail

/-- A statement of `blas%`: an update of a variable by a single routine. -/
declare_syntax_cat blasStmt

/-- `y := e` updates `y` by a single routine. -/
syntax (name := blasAssign) ident " := " blasSum : blasStmt

/-- `y += e` is `y := y + e`. -/
syntax (name := blasAddAssign) ident " += " blasSum : blasStmt

/-- `y -= e` is `y := y - e`. -/
syntax (name := blasSubAssign) ident " -= " blasSum : blasStmt

/-- The kinds of the terms that run a block: `do`, and the `blas%` blocks and terms. -/
private meta def blockKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Term.do, `BLAS.Notation.blasBlock, `BLAS.Notation.blasTerm]

/--
The target of a statement, and its routine call. A statement has no `do` block in its operands or
scalars, and no `blas%` in them, so that a block is the only `do` of its expression and each
statement is one routine.
-/
private meta def statement (s : TSyntax `blasStmt) : MacroM (Ident × Term) := do
  if let some t := s.raw.find? fun t => blockKinds.contains t.getKind then
    Macro.throwErrorAt t "blas%: no `do` or nested `blas%` in a statement; \
      bind the value with `let` first"
  let (y, call) ← match s with
    | `(blasStmt| $y:ident := $e) => pure (y, ← expand y e false false)
    | `(blasStmt| $y:ident += $e) => pure (y, ← expand y e true false)
    | `(blasStmt| $y:ident -= $e) => pure (y, ← expand y e true true)
    | _ => Macro.throwUnsupported
  -- The target `C.lower` is a view of the variable `C`, which is the matrix of the new view.
  match y.getId with
  | .str (.str p c) _ => return (mkIdentFrom y (.str p c), ← `(($call).mat))
  | _ => return (y, call)

/--
`blas% do` followed by statements, one per line, updates their targets in order, each by a single
routine. In a `do` block, the targets are mutable variables, which it reassigns.
-/
scoped syntax (name := blasDoBlock) (priority := high)
  "blas% " "do" sepBy1IndentSemicolon(blasStmt) : doElem

/-- `blas% y := e` is the block `blas% do y := e` of one statement. -/
scoped syntax (name := blasDoLine) "blas% " blasStmt : doElem

/--
As a term, `blas% do` followed by statements is the new value of the target of the last one. It
updates copies of the targets, which shadow them, as in `Id.run do let mut y := y; …; return y`.
-/
scoped syntax (name := blasBlock) "blas% " "do" sepBy1IndentSemicolon(blasStmt) : term

/--
`blas%(y := e)` is the block `blas% do y := e` of one statement as a term: the new value of `y`,
which is the routine call itself.
-/
scoped syntax (name := blasTerm) "blas%(" blasStmt ")" : term

/-- The `do` elements of the statements of a block. -/
private meta def doElems (ss : Array (TSyntax `blasStmt)) : MacroM (Array (TSyntax `doElem)) :=
  ss.mapM fun s => do
    let (y, call) ← statement s
    `(doElem| $y:ident := $call)

/-- The term of a block: the routine call of a single statement, or a `do` block otherwise. -/
private meta def block (ss : Array (TSyntax `blasStmt)) : MacroM Term := do
  if h : ss.size = 1 then
    return (← statement ss[0]).2
  let mut targets : Array Ident := #[]
  for s in ss do
    let (y, _) ← statement s
    unless targets.any (·.getId == y.getId) do targets := targets.push y
  let some last := ss.back? | Macro.throwUnsupported
  let (r, _) ← statement last
  let lets ← targets.mapM fun y => `(doElem| let mut $y:ident := $y:ident)
  let ret ← `(doElem| return $r:ident)
  let elems := lets ++ (← doElems ss) ++ #[ret]
  `(Id.run do $[$elems:doElem]*)

macro_rules (kind := blasDoBlock)
  | `(doElem| blas% do $[$ss:blasStmt]*) => do
    let elems ← doElems ss
    `(doElem| do $[$elems:doElem]*)

macro_rules (kind := blasDoLine)
  | `(doElem| blas% $s:blasStmt) => do
    let elems ← doElems #[s]
    `(doElem| do $[$elems:doElem]*)

macro_rules (kind := blasBlock)
  | `(blas% do $[$ss:blasStmt]*) => block ss

macro_rules (kind := blasTerm)
  | `(blas%($s:blasStmt)) => block #[s]

end BLAS.Notation
