import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 320–327. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P320 F [3, 5, 7, 11] 320
theorem ok320 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 320 [])) P320.sel P320.B = true := by
  decide +kernel

e4_data P321 F [3, 5, 7, 11] 321
theorem ok321 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 321 [])) P321.sel P321.B = true := by
  decide +kernel

e4_data P322 F [3, 5, 7, 11] 322
theorem ok322 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 322 [])) P322.sel P322.B = true := by
  decide +kernel

e4_data P323 F [3, 5, 7, 11] 323
theorem ok323 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 323 [])) P323.sel P323.B = true := by
  decide +kernel

e4_data P324 F [3, 5, 7, 11] 324
theorem ok324 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 324 [])) P324.sel P324.B = true := by
  decide +kernel

e4_data P325 F [3, 5, 7, 11] 325
theorem ok325 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 325 [])) P325.sel P325.B = true := by
  decide +kernel

e4_data P326 F [3, 5, 7, 11] 326
theorem ok326 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 326 [])) P326.sel P326.B = true := by
  decide +kernel

e4_data P327 F [3, 5, 7, 11] 327
theorem ok327 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 327 [])) P327.sel P327.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
