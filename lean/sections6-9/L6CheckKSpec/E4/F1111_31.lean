import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 248–255. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P248 F [1, 1, 1, 1] 248
theorem ok248 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 248 [])) P248.sel P248.B = true := by
  decide +kernel

e4_data P249 F [1, 1, 1, 1] 249
theorem ok249 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 249 [])) P249.sel P249.B = true := by
  decide +kernel

e4_data P250 F [1, 1, 1, 1] 250
theorem ok250 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 250 [])) P250.sel P250.B = true := by
  decide +kernel

e4_data P251 F [1, 1, 1, 1] 251
theorem ok251 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 251 [])) P251.sel P251.B = true := by
  decide +kernel

e4_data P252 F [1, 1, 1, 1] 252
theorem ok252 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 252 [])) P252.sel P252.B = true := by
  decide +kernel

e4_data P253 F [1, 1, 1, 1] 253
theorem ok253 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 253 [])) P253.sel P253.B = true := by
  decide +kernel

e4_data P254 F [1, 1, 1, 1] 254
theorem ok254 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 254 [])) P254.sel P254.B = true := by
  decide +kernel

e4_data P255 F [1, 1, 1, 1] 255
theorem ok255 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 255 [])) P255.sel P255.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
