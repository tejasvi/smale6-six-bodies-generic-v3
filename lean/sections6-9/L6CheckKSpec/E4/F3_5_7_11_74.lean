import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 592–599. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P592 F [3, 5, 7, 11] 592
theorem ok592 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 592 [])) P592.sel P592.B = true := by
  decide +kernel

e4_data P593 F [3, 5, 7, 11] 593
theorem ok593 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 593 [])) P593.sel P593.B = true := by
  decide +kernel

e4_data P594 F [3, 5, 7, 11] 594
theorem ok594 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 594 [])) P594.sel P594.B = true := by
  decide +kernel

e4_data P595 F [3, 5, 7, 11] 595
theorem ok595 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 595 [])) P595.sel P595.B = true := by
  decide +kernel

e4_data P596 F [3, 5, 7, 11] 596
theorem ok596 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 596 [])) P596.sel P596.B = true := by
  decide +kernel

e4_data P597 F [3, 5, 7, 11] 597
theorem ok597 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 597 [])) P597.sel P597.B = true := by
  decide +kernel

e4_data P598 F [3, 5, 7, 11] 598
theorem ok598 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 598 [])) P598.sel P598.B = true := by
  decide +kernel

e4_data P599 F [3, 5, 7, 11] 599
theorem ok599 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 599 [])) P599.sel P599.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
