import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 488–495. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P488 F [3, 5, 7, 11] 488
theorem ok488 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 488 [])) P488.sel P488.B = true := by
  decide +kernel

e4_data P489 F [3, 5, 7, 11] 489
theorem ok489 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 489 [])) P489.sel P489.B = true := by
  decide +kernel

e4_data P490 F [3, 5, 7, 11] 490
theorem ok490 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 490 [])) P490.sel P490.B = true := by
  decide +kernel

e4_data P491 F [3, 5, 7, 11] 491
theorem ok491 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 491 [])) P491.sel P491.B = true := by
  decide +kernel

e4_data P492 F [3, 5, 7, 11] 492
theorem ok492 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 492 [])) P492.sel P492.B = true := by
  decide +kernel

e4_data P493 F [3, 5, 7, 11] 493
theorem ok493 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 493 [])) P493.sel P493.B = true := by
  decide +kernel

e4_data P494 F [3, 5, 7, 11] 494
theorem ok494 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 494 [])) P494.sel P494.B = true := by
  decide +kernel

e4_data P495 F [3, 5, 7, 11] 495
theorem ok495 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 495 [])) P495.sel P495.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
