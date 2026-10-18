import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 240–247. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P240 F [3, 5, 7, 11] 240
theorem ok240 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 240 [])) P240.sel P240.B = true := by
  decide +kernel

e4_data P241 F [3, 5, 7, 11] 241
theorem ok241 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 241 [])) P241.sel P241.B = true := by
  decide +kernel

e4_data P242 F [3, 5, 7, 11] 242
theorem ok242 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 242 [])) P242.sel P242.B = true := by
  decide +kernel

e4_data P243 F [3, 5, 7, 11] 243
theorem ok243 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 243 [])) P243.sel P243.B = true := by
  decide +kernel

e4_data P244 F [3, 5, 7, 11] 244
theorem ok244 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 244 [])) P244.sel P244.B = true := by
  decide +kernel

e4_data P245 F [3, 5, 7, 11] 245
theorem ok245 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 245 [])) P245.sel P245.B = true := by
  decide +kernel

e4_data P246 F [3, 5, 7, 11] 246
theorem ok246 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 246 [])) P246.sel P246.B = true := by
  decide +kernel

e4_data P247 F [3, 5, 7, 11] 247
theorem ok247 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 247 [])) P247.sel P247.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
