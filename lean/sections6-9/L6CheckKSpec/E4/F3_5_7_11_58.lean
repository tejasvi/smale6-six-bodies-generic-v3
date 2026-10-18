import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 464–471. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P464 F [3, 5, 7, 11] 464
theorem ok464 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 464 [])) P464.sel P464.B = true := by
  decide +kernel

e4_data P465 F [3, 5, 7, 11] 465
theorem ok465 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 465 [])) P465.sel P465.B = true := by
  decide +kernel

e4_data P466 F [3, 5, 7, 11] 466
theorem ok466 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 466 [])) P466.sel P466.B = true := by
  decide +kernel

e4_data P467 F [3, 5, 7, 11] 467
theorem ok467 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 467 [])) P467.sel P467.B = true := by
  decide +kernel

e4_data P468 F [3, 5, 7, 11] 468
theorem ok468 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 468 [])) P468.sel P468.B = true := by
  decide +kernel

e4_data P469 F [3, 5, 7, 11] 469
theorem ok469 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 469 [])) P469.sel P469.B = true := by
  decide +kernel

e4_data P470 F [3, 5, 7, 11] 470
theorem ok470 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 470 [])) P470.sel P470.B = true := by
  decide +kernel

e4_data P471 F [3, 5, 7, 11] 471
theorem ok471 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 471 [])) P471.sel P471.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
