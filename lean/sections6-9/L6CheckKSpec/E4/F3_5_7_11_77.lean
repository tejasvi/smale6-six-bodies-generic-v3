import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 616–623. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P616 F [3, 5, 7, 11] 616
theorem ok616 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 616 [])) P616.sel P616.B = true := by
  decide +kernel

e4_data P617 F [3, 5, 7, 11] 617
theorem ok617 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 617 [])) P617.sel P617.B = true := by
  decide +kernel

e4_data P618 F [3, 5, 7, 11] 618
theorem ok618 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 618 [])) P618.sel P618.B = true := by
  decide +kernel

e4_data P619 F [3, 5, 7, 11] 619
theorem ok619 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 619 [])) P619.sel P619.B = true := by
  decide +kernel

e4_data P620 F [3, 5, 7, 11] 620
theorem ok620 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 620 [])) P620.sel P620.B = true := by
  decide +kernel

e4_data P621 F [3, 5, 7, 11] 621
theorem ok621 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 621 [])) P621.sel P621.B = true := by
  decide +kernel

e4_data P622 F [3, 5, 7, 11] 622
theorem ok622 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 622 [])) P622.sel P622.B = true := by
  decide +kernel

e4_data P623 F [3, 5, 7, 11] 623
theorem ok623 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 623 [])) P623.sel P623.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
