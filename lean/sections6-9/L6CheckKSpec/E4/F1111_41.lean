import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 328–335. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P328 F [1, 1, 1, 1] 328
theorem ok328 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 328 [])) P328.sel P328.B = true := by
  decide +kernel

e4_data P329 F [1, 1, 1, 1] 329
theorem ok329 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 329 [])) P329.sel P329.B = true := by
  decide +kernel

e4_data P330 F [1, 1, 1, 1] 330
theorem ok330 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 330 [])) P330.sel P330.B = true := by
  decide +kernel

e4_data P331 F [1, 1, 1, 1] 331
theorem ok331 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 331 [])) P331.sel P331.B = true := by
  decide +kernel

e4_data P332 F [1, 1, 1, 1] 332
theorem ok332 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 332 [])) P332.sel P332.B = true := by
  decide +kernel

e4_data P333 F [1, 1, 1, 1] 333
theorem ok333 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 333 [])) P333.sel P333.B = true := by
  decide +kernel

e4_data P334 F [1, 1, 1, 1] 334
theorem ok334 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 334 [])) P334.sel P334.B = true := by
  decide +kernel

e4_data P335 F [1, 1, 1, 1] 335
theorem ok335 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 335 [])) P335.sel P335.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
