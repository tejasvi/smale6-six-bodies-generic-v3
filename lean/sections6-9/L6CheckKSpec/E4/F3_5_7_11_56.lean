import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 448–455. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P448 F [3, 5, 7, 11] 448
theorem ok448 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 448 [])) P448.sel P448.B = true := by
  decide +kernel

e4_data P449 F [3, 5, 7, 11] 449
theorem ok449 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 449 [])) P449.sel P449.B = true := by
  decide +kernel

e4_data P450 F [3, 5, 7, 11] 450
theorem ok450 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 450 [])) P450.sel P450.B = true := by
  decide +kernel

e4_data P451 F [3, 5, 7, 11] 451
theorem ok451 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 451 [])) P451.sel P451.B = true := by
  decide +kernel

e4_data P452 F [3, 5, 7, 11] 452
theorem ok452 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 452 [])) P452.sel P452.B = true := by
  decide +kernel

e4_data P453 F [3, 5, 7, 11] 453
theorem ok453 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 453 [])) P453.sel P453.B = true := by
  decide +kernel

e4_data P454 F [3, 5, 7, 11] 454
theorem ok454 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 454 [])) P454.sel P454.B = true := by
  decide +kernel

e4_data P455 F [3, 5, 7, 11] 455
theorem ok455 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 455 [])) P455.sel P455.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
