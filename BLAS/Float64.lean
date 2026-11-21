/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Vec
public import BLAS.Float64.Loop
public import BLAS.Float64.Level1
public import BLAS.Float64.Rot
public import BLAS.Float64.PMat
public import BLAS.Float64.Mat
public import BLAS.Float64.Level2
public import BLAS.Float64.Trsv
public import BLAS.Float64.Syrk
public import BLAS.Float64.Level3
public import BLAS.Float64.GemmBlocked
public import BLAS.Float64.Gemm
public import BLAS.Float64.GemmT
public import BLAS.Float64.TrsvT
public import BLAS.Float64.Trmv
public import BLAS.Float64.Trsm
public import BLAS.Float64.TrsmT
public import BLAS.Float64.Trmm
public import BLAS.Float64.TrmmRight
public import BLAS.Float64.Symv
public import BLAS.Float64.Symm
public import BLAS.Float64.Syr
public import BLAS.Float64.Syr2k
public import BLAS.Float64.Gemmtr
public import BLAS.Float64.Gbmv
public import BLAS.Float64.Sbmv
public import BLAS.Float64.Tbmv
public import BLAS.Float64.Tbsv
public import BLAS.Float64.Packed
public import BLAS.Float64.Tpmv
public import BLAS.Float64.Tpsv
public import BLAS.Float64.Spmv
public import BLAS.Float64.Spr
public import BLAS.Float64.View
public import BLAS.Float64.BandView
public import BLAS.Float64.PackedView

/-!
# BLAS on `Float`

The routines on vectors and matrices of `Float`, stored in `Float64Array`s.
-/
