import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 672–679. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P672 F [3, 5, 7, 11] 672
theorem ok672 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 672 [])) P672.sel P672.B = true := by
  decide +kernel

e4_data P673 F [3, 5, 7, 11] 673
theorem ok673 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 673 [])) P673.sel P673.B = true := by
  decide +kernel

e4_data P674 F [3, 5, 7, 11] 674
theorem ok674 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 674 [])) P674.sel P674.B = true := by
  decide +kernel

e4_data P675 F [3, 5, 7, 11] 675
theorem ok675 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 675 [])) P675.sel P675.B = true := by
  decide +kernel

e4_data P676 F [3, 5, 7, 11] 676
theorem ok676 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 676 [])) P676.sel P676.B = true := by
  decide +kernel

e4_data P677 F [3, 5, 7, 11] 677
theorem ok677 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 677 [])) P677.sel P677.B = true := by
  decide +kernel

e4_data P678 F [3, 5, 7, 11] 678
theorem ok678 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 678 [])) P678.sel P678.B = true := by
  decide +kernel

e4_data P679 F [3, 5, 7, 11] 679
theorem ok679 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 679 [])) P679.sel P679.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
