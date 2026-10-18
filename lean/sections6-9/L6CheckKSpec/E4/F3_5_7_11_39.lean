import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 312–319. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P312 F [3, 5, 7, 11] 312
theorem ok312 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 312 [])) P312.sel P312.B = true := by
  decide +kernel

e4_data P313 F [3, 5, 7, 11] 313
theorem ok313 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 313 [])) P313.sel P313.B = true := by
  decide +kernel

e4_data P314 F [3, 5, 7, 11] 314
theorem ok314 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 314 [])) P314.sel P314.B = true := by
  decide +kernel

e4_data P315 F [3, 5, 7, 11] 315
theorem ok315 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 315 [])) P315.sel P315.B = true := by
  decide +kernel

e4_data P316 F [3, 5, 7, 11] 316
theorem ok316 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 316 [])) P316.sel P316.B = true := by
  decide +kernel

e4_data P317 F [3, 5, 7, 11] 317
theorem ok317 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 317 [])) P317.sel P317.B = true := by
  decide +kernel

e4_data P318 F [3, 5, 7, 11] 318
theorem ok318 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 318 [])) P318.sel P318.B = true := by
  decide +kernel

e4_data P319 F [3, 5, 7, 11] 319
theorem ok319 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 319 [])) P319.sel P319.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
