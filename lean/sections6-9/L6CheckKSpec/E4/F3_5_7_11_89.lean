import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 712–719. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P712 F [3, 5, 7, 11] 712
theorem ok712 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 712 [])) P712.sel P712.B = true := by
  decide +kernel

e4_data P713 F [3, 5, 7, 11] 713
theorem ok713 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 713 [])) P713.sel P713.B = true := by
  decide +kernel

e4_data P714 F [3, 5, 7, 11] 714
theorem ok714 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 714 [])) P714.sel P714.B = true := by
  decide +kernel

e4_data P715 F [3, 5, 7, 11] 715
theorem ok715 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 715 [])) P715.sel P715.B = true := by
  decide +kernel

e4_data P716 F [3, 5, 7, 11] 716
theorem ok716 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 716 [])) P716.sel P716.B = true := by
  decide +kernel

e4_data P717 F [3, 5, 7, 11] 717
theorem ok717 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 717 [])) P717.sel P717.B = true := by
  decide +kernel

e4_data P718 F [3, 5, 7, 11] 718
theorem ok718 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 718 [])) P718.sel P718.B = true := by
  decide +kernel

e4_data P719 F [3, 5, 7, 11] 719
theorem ok719 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 719 [])) P719.sel P719.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
