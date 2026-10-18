import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 624–631. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P624 F [3, 5, 7, 11] 624
theorem ok624 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 624 [])) P624.sel P624.B = true := by
  decide +kernel

e4_data P625 F [3, 5, 7, 11] 625
theorem ok625 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 625 [])) P625.sel P625.B = true := by
  decide +kernel

e4_data P626 F [3, 5, 7, 11] 626
theorem ok626 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 626 [])) P626.sel P626.B = true := by
  decide +kernel

e4_data P627 F [3, 5, 7, 11] 627
theorem ok627 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 627 [])) P627.sel P627.B = true := by
  decide +kernel

e4_data P628 F [3, 5, 7, 11] 628
theorem ok628 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 628 [])) P628.sel P628.B = true := by
  decide +kernel

e4_data P629 F [3, 5, 7, 11] 629
theorem ok629 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 629 [])) P629.sel P629.B = true := by
  decide +kernel

e4_data P630 F [3, 5, 7, 11] 630
theorem ok630 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 630 [])) P630.sel P630.B = true := by
  decide +kernel

e4_data P631 F [3, 5, 7, 11] 631
theorem ok631 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 631 [])) P631.sel P631.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
