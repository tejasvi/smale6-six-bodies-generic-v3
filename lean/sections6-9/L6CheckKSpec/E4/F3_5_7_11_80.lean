import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 640–647. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P640 F [3, 5, 7, 11] 640
theorem ok640 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 640 [])) P640.sel P640.B = true := by
  decide +kernel

e4_data P641 F [3, 5, 7, 11] 641
theorem ok641 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 641 [])) P641.sel P641.B = true := by
  decide +kernel

e4_data P642 F [3, 5, 7, 11] 642
theorem ok642 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 642 [])) P642.sel P642.B = true := by
  decide +kernel

e4_data P643 F [3, 5, 7, 11] 643
theorem ok643 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 643 [])) P643.sel P643.B = true := by
  decide +kernel

e4_data P644 F [3, 5, 7, 11] 644
theorem ok644 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 644 [])) P644.sel P644.B = true := by
  decide +kernel

e4_data P645 F [3, 5, 7, 11] 645
theorem ok645 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 645 [])) P645.sel P645.B = true := by
  decide +kernel

e4_data P646 F [3, 5, 7, 11] 646
theorem ok646 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 646 [])) P646.sel P646.B = true := by
  decide +kernel

e4_data P647 F [3, 5, 7, 11] 647
theorem ok647 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 647 [])) P647.sel P647.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
