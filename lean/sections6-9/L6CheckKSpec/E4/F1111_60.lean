import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 480–487. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P480 F [1, 1, 1, 1] 480
theorem ok480 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 480 [])) P480.sel P480.B = true := by
  decide +kernel

e4_data P481 F [1, 1, 1, 1] 481
theorem ok481 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 481 [])) P481.sel P481.B = true := by
  decide +kernel

e4_data P482 F [1, 1, 1, 1] 482
theorem ok482 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 482 [])) P482.sel P482.B = true := by
  decide +kernel

e4_data P483 F [1, 1, 1, 1] 483
theorem ok483 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 483 [])) P483.sel P483.B = true := by
  decide +kernel

e4_data P484 F [1, 1, 1, 1] 484
theorem ok484 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 484 [])) P484.sel P484.B = true := by
  decide +kernel

e4_data P485 F [1, 1, 1, 1] 485
theorem ok485 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 485 [])) P485.sel P485.B = true := by
  decide +kernel

e4_data P486 F [1, 1, 1, 1] 486
theorem ok486 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 486 [])) P486.sel P486.B = true := by
  decide +kernel

e4_data P487 F [1, 1, 1, 1] 487
theorem ok487 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 487 [])) P487.sel P487.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
