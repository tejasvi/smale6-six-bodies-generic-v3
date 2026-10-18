import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 536–543. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P536 F [3, 5, 7, 11] 536
theorem ok536 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 536 [])) P536.sel P536.B = true := by
  decide +kernel

e4_data P537 F [3, 5, 7, 11] 537
theorem ok537 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 537 [])) P537.sel P537.B = true := by
  decide +kernel

e4_data P538 F [3, 5, 7, 11] 538
theorem ok538 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 538 [])) P538.sel P538.B = true := by
  decide +kernel

e4_data P539 F [3, 5, 7, 11] 539
theorem ok539 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 539 [])) P539.sel P539.B = true := by
  decide +kernel

e4_data P540 F [3, 5, 7, 11] 540
theorem ok540 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 540 [])) P540.sel P540.B = true := by
  decide +kernel

e4_data P541 F [3, 5, 7, 11] 541
theorem ok541 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 541 [])) P541.sel P541.B = true := by
  decide +kernel

e4_data P542 F [3, 5, 7, 11] 542
theorem ok542 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 542 [])) P542.sel P542.B = true := by
  decide +kernel

e4_data P543 F [3, 5, 7, 11] 543
theorem ok543 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 543 [])) P543.sel P543.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
