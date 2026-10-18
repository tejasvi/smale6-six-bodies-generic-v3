import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 304–311. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P304 F [3, 5, 7, 11] 304
theorem ok304 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 304 [])) P304.sel P304.B = true := by
  decide +kernel

e4_data P305 F [3, 5, 7, 11] 305
theorem ok305 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 305 [])) P305.sel P305.B = true := by
  decide +kernel

e4_data P306 F [3, 5, 7, 11] 306
theorem ok306 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 306 [])) P306.sel P306.B = true := by
  decide +kernel

e4_data P307 F [3, 5, 7, 11] 307
theorem ok307 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 307 [])) P307.sel P307.B = true := by
  decide +kernel

e4_data P308 F [3, 5, 7, 11] 308
theorem ok308 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 308 [])) P308.sel P308.B = true := by
  decide +kernel

e4_data P309 F [3, 5, 7, 11] 309
theorem ok309 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 309 [])) P309.sel P309.B = true := by
  decide +kernel

e4_data P310 F [3, 5, 7, 11] 310
theorem ok310 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 310 [])) P310.sel P310.B = true := by
  decide +kernel

e4_data P311 F [3, 5, 7, 11] 311
theorem ok311 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 311 [])) P311.sel P311.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
