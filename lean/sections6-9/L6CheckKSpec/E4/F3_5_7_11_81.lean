import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 648–655. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P648 F [3, 5, 7, 11] 648
theorem ok648 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 648 [])) P648.sel P648.B = true := by
  decide +kernel

e4_data P649 F [3, 5, 7, 11] 649
theorem ok649 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 649 [])) P649.sel P649.B = true := by
  decide +kernel

e4_data P650 F [3, 5, 7, 11] 650
theorem ok650 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 650 [])) P650.sel P650.B = true := by
  decide +kernel

e4_data P651 F [3, 5, 7, 11] 651
theorem ok651 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 651 [])) P651.sel P651.B = true := by
  decide +kernel

e4_data P652 F [3, 5, 7, 11] 652
theorem ok652 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 652 [])) P652.sel P652.B = true := by
  decide +kernel

e4_data P653 F [3, 5, 7, 11] 653
theorem ok653 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 653 [])) P653.sel P653.B = true := by
  decide +kernel

e4_data P654 F [3, 5, 7, 11] 654
theorem ok654 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 654 [])) P654.sel P654.B = true := by
  decide +kernel

e4_data P655 F [3, 5, 7, 11] 655
theorem ok655 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 655 [])) P655.sel P655.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
