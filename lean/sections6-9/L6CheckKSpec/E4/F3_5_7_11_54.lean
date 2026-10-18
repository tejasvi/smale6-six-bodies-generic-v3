import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 432–439. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P432 F [3, 5, 7, 11] 432
theorem ok432 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 432 [])) P432.sel P432.B = true := by
  decide +kernel

e4_data P433 F [3, 5, 7, 11] 433
theorem ok433 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 433 [])) P433.sel P433.B = true := by
  decide +kernel

e4_data P434 F [3, 5, 7, 11] 434
theorem ok434 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 434 [])) P434.sel P434.B = true := by
  decide +kernel

e4_data P435 F [3, 5, 7, 11] 435
theorem ok435 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 435 [])) P435.sel P435.B = true := by
  decide +kernel

e4_data P436 F [3, 5, 7, 11] 436
theorem ok436 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 436 [])) P436.sel P436.B = true := by
  decide +kernel

e4_data P437 F [3, 5, 7, 11] 437
theorem ok437 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 437 [])) P437.sel P437.B = true := by
  decide +kernel

e4_data P438 F [3, 5, 7, 11] 438
theorem ok438 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 438 [])) P438.sel P438.B = true := by
  decide +kernel

e4_data P439 F [3, 5, 7, 11] 439
theorem ok439 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 439 [])) P439.sel P439.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
