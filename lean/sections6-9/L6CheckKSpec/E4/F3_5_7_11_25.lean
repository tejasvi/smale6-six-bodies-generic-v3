import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 200–207. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P200 F [3, 5, 7, 11] 200
theorem ok200 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 200 [])) P200.sel P200.B = true := by
  decide +kernel

e4_data P201 F [3, 5, 7, 11] 201
theorem ok201 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 201 [])) P201.sel P201.B = true := by
  decide +kernel

e4_data P202 F [3, 5, 7, 11] 202
theorem ok202 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 202 [])) P202.sel P202.B = true := by
  decide +kernel

e4_data P203 F [3, 5, 7, 11] 203
theorem ok203 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 203 [])) P203.sel P203.B = true := by
  decide +kernel

e4_data P204 F [3, 5, 7, 11] 204
theorem ok204 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 204 [])) P204.sel P204.B = true := by
  decide +kernel

e4_data P205 F [3, 5, 7, 11] 205
theorem ok205 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 205 [])) P205.sel P205.B = true := by
  decide +kernel

e4_data P206 F [3, 5, 7, 11] 206
theorem ok206 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 206 [])) P206.sel P206.B = true := by
  decide +kernel

e4_data P207 F [3, 5, 7, 11] 207
theorem ok207 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 207 [])) P207.sel P207.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
