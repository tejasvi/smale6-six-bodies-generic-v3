import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 112–119. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P112 F [3, 5, 7, 11] 112
theorem ok112 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 112 [])) P112.sel P112.B = true := by
  decide +kernel

e4_data P113 F [3, 5, 7, 11] 113
theorem ok113 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 113 [])) P113.sel P113.B = true := by
  decide +kernel

e4_data P114 F [3, 5, 7, 11] 114
theorem ok114 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 114 [])) P114.sel P114.B = true := by
  decide +kernel

e4_data P115 F [3, 5, 7, 11] 115
theorem ok115 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 115 [])) P115.sel P115.B = true := by
  decide +kernel

e4_data P116 F [3, 5, 7, 11] 116
theorem ok116 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 116 [])) P116.sel P116.B = true := by
  decide +kernel

e4_data P117 F [3, 5, 7, 11] 117
theorem ok117 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 117 [])) P117.sel P117.B = true := by
  decide +kernel

e4_data P118 F [3, 5, 7, 11] 118
theorem ok118 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 118 [])) P118.sel P118.B = true := by
  decide +kernel

e4_data P119 F [3, 5, 7, 11] 119
theorem ok119 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 119 [])) P119.sel P119.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
