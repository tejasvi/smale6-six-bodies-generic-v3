import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 600–607. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P600 F [1, 1, 1, 1] 600
theorem ok600 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 600 [])) P600.sel P600.B = true := by
  decide +kernel

e4_data P601 F [1, 1, 1, 1] 601
theorem ok601 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 601 [])) P601.sel P601.B = true := by
  decide +kernel

e4_data P602 F [1, 1, 1, 1] 602
theorem ok602 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 602 [])) P602.sel P602.B = true := by
  decide +kernel

e4_data P603 F [1, 1, 1, 1] 603
theorem ok603 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 603 [])) P603.sel P603.B = true := by
  decide +kernel

e4_data P604 F [1, 1, 1, 1] 604
theorem ok604 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 604 [])) P604.sel P604.B = true := by
  decide +kernel

e4_data P605 F [1, 1, 1, 1] 605
theorem ok605 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 605 [])) P605.sel P605.B = true := by
  decide +kernel

e4_data P606 F [1, 1, 1, 1] 606
theorem ok606 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 606 [])) P606.sel P606.B = true := by
  decide +kernel

e4_data P607 F [1, 1, 1, 1] 607
theorem ok607 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 607 [])) P607.sel P607.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
