import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 376–383. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P376 F [1, 1, 1, 1] 376
theorem ok376 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 376 [])) P376.sel P376.B = true := by
  decide +kernel

e4_data P377 F [1, 1, 1, 1] 377
theorem ok377 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 377 [])) P377.sel P377.B = true := by
  decide +kernel

e4_data P378 F [1, 1, 1, 1] 378
theorem ok378 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 378 [])) P378.sel P378.B = true := by
  decide +kernel

e4_data P379 F [1, 1, 1, 1] 379
theorem ok379 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 379 [])) P379.sel P379.B = true := by
  decide +kernel

e4_data P380 F [1, 1, 1, 1] 380
theorem ok380 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 380 [])) P380.sel P380.B = true := by
  decide +kernel

e4_data P381 F [1, 1, 1, 1] 381
theorem ok381 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 381 [])) P381.sel P381.B = true := by
  decide +kernel

e4_data P382 F [1, 1, 1, 1] 382
theorem ok382 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 382 [])) P382.sel P382.B = true := by
  decide +kernel

e4_data P383 F [1, 1, 1, 1] 383
theorem ok383 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 383 [])) P383.sel P383.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
