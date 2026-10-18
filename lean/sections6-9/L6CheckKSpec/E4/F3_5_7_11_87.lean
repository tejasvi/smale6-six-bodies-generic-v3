import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 696–703. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P696 F [3, 5, 7, 11] 696
theorem ok696 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 696 [])) P696.sel P696.B = true := by
  decide +kernel

e4_data P697 F [3, 5, 7, 11] 697
theorem ok697 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 697 [])) P697.sel P697.B = true := by
  decide +kernel

e4_data P698 F [3, 5, 7, 11] 698
theorem ok698 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 698 [])) P698.sel P698.B = true := by
  decide +kernel

e4_data P699 F [3, 5, 7, 11] 699
theorem ok699 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 699 [])) P699.sel P699.B = true := by
  decide +kernel

e4_data P700 F [3, 5, 7, 11] 700
theorem ok700 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 700 [])) P700.sel P700.B = true := by
  decide +kernel

e4_data P701 F [3, 5, 7, 11] 701
theorem ok701 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 701 [])) P701.sel P701.B = true := by
  decide +kernel

e4_data P702 F [3, 5, 7, 11] 702
theorem ok702 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 702 [])) P702.sel P702.B = true := by
  decide +kernel

e4_data P703 F [3, 5, 7, 11] 703
theorem ok703 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 703 [])) P703.sel P703.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
