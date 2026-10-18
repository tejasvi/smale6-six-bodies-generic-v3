import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 432–439. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P432 F [1, 1, 1, 1] 432
theorem ok432 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 432 [])) P432.sel P432.B = true := by
  decide +kernel

e4_data P433 F [1, 1, 1, 1] 433
theorem ok433 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 433 [])) P433.sel P433.B = true := by
  decide +kernel

e4_data P434 F [1, 1, 1, 1] 434
theorem ok434 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 434 [])) P434.sel P434.B = true := by
  decide +kernel

e4_data P435 F [1, 1, 1, 1] 435
theorem ok435 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 435 [])) P435.sel P435.B = true := by
  decide +kernel

e4_data P436 F [1, 1, 1, 1] 436
theorem ok436 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 436 [])) P436.sel P436.B = true := by
  decide +kernel

e4_data P437 F [1, 1, 1, 1] 437
theorem ok437 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 437 [])) P437.sel P437.B = true := by
  decide +kernel

e4_data P438 F [1, 1, 1, 1] 438
theorem ok438 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 438 [])) P438.sel P438.B = true := by
  decide +kernel

e4_data P439 F [1, 1, 1, 1] 439
theorem ok439 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 439 [])) P439.sel P439.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
