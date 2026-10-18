import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 680–687. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P680 F [1, 1, 1, 1] 680
theorem ok680 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 680 [])) P680.sel P680.B = true := by
  decide +kernel

e4_data P681 F [1, 1, 1, 1] 681
theorem ok681 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 681 [])) P681.sel P681.B = true := by
  decide +kernel

e4_data P682 F [1, 1, 1, 1] 682
theorem ok682 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 682 [])) P682.sel P682.B = true := by
  decide +kernel

e4_data P683 F [1, 1, 1, 1] 683
theorem ok683 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 683 [])) P683.sel P683.B = true := by
  decide +kernel

e4_data P684 F [1, 1, 1, 1] 684
theorem ok684 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 684 [])) P684.sel P684.B = true := by
  decide +kernel

e4_data P685 F [1, 1, 1, 1] 685
theorem ok685 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 685 [])) P685.sel P685.B = true := by
  decide +kernel

e4_data P686 F [1, 1, 1, 1] 686
theorem ok686 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 686 [])) P686.sel P686.B = true := by
  decide +kernel

e4_data P687 F [1, 1, 1, 1] 687
theorem ok687 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 687 [])) P687.sel P687.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
