/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
meta import BLAS

/-!
Checks that the compiled code of scalar-arrays runs in the tests, which the routines' tests rely on.
-/

open ScalarArray

#guard (Float64Array.replicate 3 1.5).size == 3
#guard (Float64Array.ofList [1, 2, 3]).foldl (· + ·) 0 == 6
