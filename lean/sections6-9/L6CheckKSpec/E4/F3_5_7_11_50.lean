import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 400–407. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P400 F [3, 5, 7, 11] 400
theorem ok400 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 400 [])) P400.sel P400.B = true := by
  decide +kernel

e4_data P401 F [3, 5, 7, 11] 401
theorem ok401 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 401 [])) P401.sel P401.B = true := by
  decide +kernel

e4_data P402 F [3, 5, 7, 11] 402
theorem ok402 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 402 [])) P402.sel P402.B = true := by
  decide +kernel

e4_data P403 F [3, 5, 7, 11] 403
theorem ok403 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 403 [])) P403.sel P403.B = true := by
  decide +kernel

e4_data P404 F [3, 5, 7, 11] 404
theorem ok404 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 404 [])) P404.sel P404.B = true := by
  decide +kernel

e4_data P405 F [3, 5, 7, 11] 405
theorem ok405 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 405 [])) P405.sel P405.B = true := by
  decide +kernel

e4_data P406 F [3, 5, 7, 11] 406
theorem ok406 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 406 [])) P406.sel P406.B = true := by
  decide +kernel

e4_data P407 F [3, 5, 7, 11] 407
theorem ok407 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 407 [])) P407.sel P407.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
