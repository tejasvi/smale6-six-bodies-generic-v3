import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 280–287. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P280 F [1, 1, 1, 1] 280
theorem ok280 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 280 [])) P280.sel P280.B = true := by
  decide +kernel

e4_data P281 F [1, 1, 1, 1] 281
theorem ok281 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 281 [])) P281.sel P281.B = true := by
  decide +kernel

e4_data P282 F [1, 1, 1, 1] 282
theorem ok282 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 282 [])) P282.sel P282.B = true := by
  decide +kernel

e4_data P283 F [1, 1, 1, 1] 283
theorem ok283 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 283 [])) P283.sel P283.B = true := by
  decide +kernel

e4_data P284 F [1, 1, 1, 1] 284
theorem ok284 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 284 [])) P284.sel P284.B = true := by
  decide +kernel

e4_data P285 F [1, 1, 1, 1] 285
theorem ok285 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 285 [])) P285.sel P285.B = true := by
  decide +kernel

e4_data P286 F [1, 1, 1, 1] 286
theorem ok286 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 286 [])) P286.sel P286.B = true := by
  decide +kernel

e4_data P287 F [1, 1, 1, 1] 287
theorem ok287 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 287 [])) P287.sel P287.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
