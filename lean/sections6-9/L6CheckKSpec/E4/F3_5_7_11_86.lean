import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 688–695. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P688 F [3, 5, 7, 11] 688
theorem ok688 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 688 [])) P688.sel P688.B = true := by
  decide +kernel

e4_data P689 F [3, 5, 7, 11] 689
theorem ok689 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 689 [])) P689.sel P689.B = true := by
  decide +kernel

e4_data P690 F [3, 5, 7, 11] 690
theorem ok690 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 690 [])) P690.sel P690.B = true := by
  decide +kernel

e4_data P691 F [3, 5, 7, 11] 691
theorem ok691 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 691 [])) P691.sel P691.B = true := by
  decide +kernel

e4_data P692 F [3, 5, 7, 11] 692
theorem ok692 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 692 [])) P692.sel P692.B = true := by
  decide +kernel

e4_data P693 F [3, 5, 7, 11] 693
theorem ok693 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 693 [])) P693.sel P693.B = true := by
  decide +kernel

e4_data P694 F [3, 5, 7, 11] 694
theorem ok694 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 694 [])) P694.sel P694.B = true := by
  decide +kernel

e4_data P695 F [3, 5, 7, 11] 695
theorem ok695 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 695 [])) P695.sel P695.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
