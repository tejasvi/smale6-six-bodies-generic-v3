import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 264–271. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P264 F [1, 1, 1, 1] 264
theorem ok264 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 264 [])) P264.sel P264.B = true := by
  decide +kernel

e4_data P265 F [1, 1, 1, 1] 265
theorem ok265 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 265 [])) P265.sel P265.B = true := by
  decide +kernel

e4_data P266 F [1, 1, 1, 1] 266
theorem ok266 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 266 [])) P266.sel P266.B = true := by
  decide +kernel

e4_data P267 F [1, 1, 1, 1] 267
theorem ok267 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 267 [])) P267.sel P267.B = true := by
  decide +kernel

e4_data P268 F [1, 1, 1, 1] 268
theorem ok268 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 268 [])) P268.sel P268.B = true := by
  decide +kernel

e4_data P269 F [1, 1, 1, 1] 269
theorem ok269 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 269 [])) P269.sel P269.B = true := by
  decide +kernel

e4_data P270 F [1, 1, 1, 1] 270
theorem ok270 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 270 [])) P270.sel P270.B = true := by
  decide +kernel

e4_data P271 F [1, 1, 1, 1] 271
theorem ok271 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 271 [])) P271.sel P271.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
