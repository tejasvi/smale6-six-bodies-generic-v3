import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 360–367. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P360 F [3, 5, 7, 11] 360
theorem ok360 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 360 [])) P360.sel P360.B = true := by
  decide +kernel

e4_data P361 F [3, 5, 7, 11] 361
theorem ok361 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 361 [])) P361.sel P361.B = true := by
  decide +kernel

e4_data P362 F [3, 5, 7, 11] 362
theorem ok362 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 362 [])) P362.sel P362.B = true := by
  decide +kernel

e4_data P363 F [3, 5, 7, 11] 363
theorem ok363 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 363 [])) P363.sel P363.B = true := by
  decide +kernel

e4_data P364 F [3, 5, 7, 11] 364
theorem ok364 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 364 [])) P364.sel P364.B = true := by
  decide +kernel

e4_data P365 F [3, 5, 7, 11] 365
theorem ok365 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 365 [])) P365.sel P365.B = true := by
  decide +kernel

e4_data P366 F [3, 5, 7, 11] 366
theorem ok366 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 366 [])) P366.sel P366.B = true := by
  decide +kernel

e4_data P367 F [3, 5, 7, 11] 367
theorem ok367 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 367 [])) P367.sel P367.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
