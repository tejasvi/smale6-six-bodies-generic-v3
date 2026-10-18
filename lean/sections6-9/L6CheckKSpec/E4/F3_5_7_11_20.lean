import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 160–167. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P160 F [3, 5, 7, 11] 160
theorem ok160 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 160 [])) P160.sel P160.B = true := by
  decide +kernel

e4_data P161 F [3, 5, 7, 11] 161
theorem ok161 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 161 [])) P161.sel P161.B = true := by
  decide +kernel

e4_data P162 F [3, 5, 7, 11] 162
theorem ok162 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 162 [])) P162.sel P162.B = true := by
  decide +kernel

e4_data P163 F [3, 5, 7, 11] 163
theorem ok163 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 163 [])) P163.sel P163.B = true := by
  decide +kernel

e4_data P164 F [3, 5, 7, 11] 164
theorem ok164 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 164 [])) P164.sel P164.B = true := by
  decide +kernel

e4_data P165 F [3, 5, 7, 11] 165
theorem ok165 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 165 [])) P165.sel P165.B = true := by
  decide +kernel

e4_data P166 F [3, 5, 7, 11] 166
theorem ok166 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 166 [])) P166.sel P166.B = true := by
  decide +kernel

e4_data P167 F [3, 5, 7, 11] 167
theorem ok167 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 167 [])) P167.sel P167.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
