import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 632–639. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P632 F [3, 5, 7, 11] 632
theorem ok632 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 632 [])) P632.sel P632.B = true := by
  decide +kernel

e4_data P633 F [3, 5, 7, 11] 633
theorem ok633 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 633 [])) P633.sel P633.B = true := by
  decide +kernel

e4_data P634 F [3, 5, 7, 11] 634
theorem ok634 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 634 [])) P634.sel P634.B = true := by
  decide +kernel

e4_data P635 F [3, 5, 7, 11] 635
theorem ok635 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 635 [])) P635.sel P635.B = true := by
  decide +kernel

e4_data P636 F [3, 5, 7, 11] 636
theorem ok636 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 636 [])) P636.sel P636.B = true := by
  decide +kernel

e4_data P637 F [3, 5, 7, 11] 637
theorem ok637 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 637 [])) P637.sel P637.B = true := by
  decide +kernel

e4_data P638 F [3, 5, 7, 11] 638
theorem ok638 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 638 [])) P638.sel P638.B = true := by
  decide +kernel

e4_data P639 F [3, 5, 7, 11] 639
theorem ok639 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 639 [])) P639.sel P639.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
