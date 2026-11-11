/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Helpers that inspect the runtime representation of a value. Their Lean definitions are
placeholders; only the compiled implementations are meaningful, which is what `#guard` runs.
-/

namespace BLASTest

private unsafe def addrImpl (a : @& α) : USize := ptrAddrUnsafe a

/-- The address of the runtime object, to check whether an operation worked in place. -/
@[implemented_by addrImpl]
public def addr {α : Type _} (_ : @& α) : USize := 0

end BLASTest
