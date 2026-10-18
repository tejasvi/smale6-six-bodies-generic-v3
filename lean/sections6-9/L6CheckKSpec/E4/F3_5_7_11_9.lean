import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 72–79. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P72 F [3, 5, 7, 11] 72
theorem ok72 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 72 [])) P72.sel P72.B = true := by
  decide +kernel

e4_data P73 F [3, 5, 7, 11] 73
theorem ok73 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 73 [])) P73.sel P73.B = true := by
  decide +kernel

e4_data P74 F [3, 5, 7, 11] 74
theorem ok74 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 74 [])) P74.sel P74.B = true := by
  decide +kernel

e4_data P75 F [3, 5, 7, 11] 75
theorem ok75 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 75 [])) P75.sel P75.B = true := by
  decide +kernel

e4_data P76 F [3, 5, 7, 11] 76
theorem ok76 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 76 [])) P76.sel P76.B = true := by
  decide +kernel

e4_data P77 F [3, 5, 7, 11] 77
theorem ok77 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 77 [])) P77.sel P77.B = true := by
  decide +kernel

e4_data P78 F [3, 5, 7, 11] 78
theorem ok78 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 78 [])) P78.sel P78.B = true := by
  decide +kernel

e4_data P79 F [3, 5, 7, 11] 79
theorem ok79 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 79 [])) P79.sel P79.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
