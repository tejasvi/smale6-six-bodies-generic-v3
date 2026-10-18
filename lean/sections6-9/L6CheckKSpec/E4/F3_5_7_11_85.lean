import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 680–687. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P680 F [3, 5, 7, 11] 680
theorem ok680 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 680 [])) P680.sel P680.B = true := by
  decide +kernel

e4_data P681 F [3, 5, 7, 11] 681
theorem ok681 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 681 [])) P681.sel P681.B = true := by
  decide +kernel

e4_data P682 F [3, 5, 7, 11] 682
theorem ok682 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 682 [])) P682.sel P682.B = true := by
  decide +kernel

e4_data P683 F [3, 5, 7, 11] 683
theorem ok683 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 683 [])) P683.sel P683.B = true := by
  decide +kernel

e4_data P684 F [3, 5, 7, 11] 684
theorem ok684 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 684 [])) P684.sel P684.B = true := by
  decide +kernel

e4_data P685 F [3, 5, 7, 11] 685
theorem ok685 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 685 [])) P685.sel P685.B = true := by
  decide +kernel

e4_data P686 F [3, 5, 7, 11] 686
theorem ok686 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 686 [])) P686.sel P686.B = true := by
  decide +kernel

e4_data P687 F [3, 5, 7, 11] 687
theorem ok687 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 687 [])) P687.sel P687.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
