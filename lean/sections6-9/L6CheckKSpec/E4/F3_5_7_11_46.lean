import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 368–375. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P368 F [3, 5, 7, 11] 368
theorem ok368 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 368 [])) P368.sel P368.B = true := by
  decide +kernel

e4_data P369 F [3, 5, 7, 11] 369
theorem ok369 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 369 [])) P369.sel P369.B = true := by
  decide +kernel

e4_data P370 F [3, 5, 7, 11] 370
theorem ok370 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 370 [])) P370.sel P370.B = true := by
  decide +kernel

e4_data P371 F [3, 5, 7, 11] 371
theorem ok371 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 371 [])) P371.sel P371.B = true := by
  decide +kernel

e4_data P372 F [3, 5, 7, 11] 372
theorem ok372 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 372 [])) P372.sel P372.B = true := by
  decide +kernel

e4_data P373 F [3, 5, 7, 11] 373
theorem ok373 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 373 [])) P373.sel P373.B = true := by
  decide +kernel

e4_data P374 F [3, 5, 7, 11] 374
theorem ok374 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 374 [])) P374.sel P374.B = true := by
  decide +kernel

e4_data P375 F [3, 5, 7, 11] 375
theorem ok375 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 375 [])) P375.sel P375.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
