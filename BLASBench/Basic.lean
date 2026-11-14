/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray

/-!
# The benchmark harness

Timing, the rows of the results and the sizes of the benchmarks of `lake exe bench`, which don't
depend on the precision.
-/

open ScalarArray

namespace BLASBench

public section

/--
Runs `f` and returns its result. It is not inlined, so `f` runs exactly when this action does,
between the clock readings around it.
-/
@[noinline] def run {α : Type} (f : Nat → α) (n : Nat) : IO α := pure (f n)

/-- The fastest of `rounds` runs of `f n`, in milliseconds. -/
def time {α : Type} [Add α] [OfNat α 0] [OfScientific α] [BEq α] (rounds n : Nat) (f : Nat → α) :
    IO Float := do
  let mut best := (0 : UInt64) - 1
  let mut sink : α := 0
  for _ in [0:rounds] do
    let t₀ ← IO.monoNanosNow
    sink := sink + (← run f n)
    let t₁ ← IO.monoNanosNow
    best := min best (t₁ - t₀).toUInt64
  -- Keeps the results live.
  if sink == 0.125 then IO.eprintln ""
  return best.toFloat / 1e6

/-- One line of the results. -/
structure Row where
  /-- The benchmark's name. -/
  name : String
  /-- The time for `BLAS`, in milliseconds. -/
  time : Float
  /-- The time for the reference, in milliseconds, if there is one. -/
  ref : Option Float

/-- The number of times each update runs per round: the first copies the shared input. -/
def reps : Nat := 10

/-- The sizes of the Level 2 benchmarks. -/
def level2Sizes : List Nat := [256, 1024, 2048]

/-- The sizes of the `syrk` and `trsm` benchmarks. -/
def level3Sizes : List Nat := [256, 512, 1024]

/-- The sizes of the `gemm` benchmarks. -/
def gemmSizes : List Nat := [64, 256, 512, 1024]

/--
A baseline for the harness: a plain read-only loop over a `Float64Array` of `n` elements, against
the same loop over a core `FloatArray`.
-/
def baseline (rounds n : Nat) : IO Row := do
  let x : Float64Array := .ofFn (n := n) fun i => (i.val % 7).toFloat - 3
  let x' := x.toFloatArray
  let sum ← time rounds n fun _ => x.foldl (· + ·) 0
  let sum' ← time rounds n fun _ => x'.foldl (· + ·) 0
  return ⟨"sum (baseline)", sum, some sum'⟩

/-- A time in milliseconds with three decimals. -/
def fmt (t : Float) : String :=
  let s := toString ((t * 1000).round / 1000)
  match s.splitOn "." with
  | [i, f] => i ++ "." ++ (f ++ "000").take 3
  | _ => s

end

end BLASBench
