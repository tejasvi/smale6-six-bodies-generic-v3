import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 232–239. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P232 F [3, 5, 7, 11] 232
theorem ok232 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 232 [])) P232.sel P232.B = true := by
  decide +kernel

e4_data P233 F [3, 5, 7, 11] 233
theorem ok233 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 233 [])) P233.sel P233.B = true := by
  decide +kernel

e4_data P234 F [3, 5, 7, 11] 234
theorem ok234 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 234 [])) P234.sel P234.B = true := by
  decide +kernel

e4_data P235 F [3, 5, 7, 11] 235
theorem ok235 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 235 [])) P235.sel P235.B = true := by
  decide +kernel

e4_data P236 F [3, 5, 7, 11] 236
theorem ok236 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 236 [])) P236.sel P236.B = true := by
  decide +kernel

e4_data P237 F [3, 5, 7, 11] 237
theorem ok237 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 237 [])) P237.sel P237.B = true := by
  decide +kernel

e4_data P238 F [3, 5, 7, 11] 238
theorem ok238 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 238 [])) P238.sel P238.B = true := by
  decide +kernel

e4_data P239 F [3, 5, 7, 11] 239
theorem ok239 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 239 [])) P239.sel P239.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
