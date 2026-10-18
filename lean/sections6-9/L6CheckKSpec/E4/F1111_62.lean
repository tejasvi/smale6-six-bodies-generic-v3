import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 496–503. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P496 F [1, 1, 1, 1] 496
theorem ok496 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 496 [])) P496.sel P496.B = true := by
  decide +kernel

e4_data P497 F [1, 1, 1, 1] 497
theorem ok497 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 497 [])) P497.sel P497.B = true := by
  decide +kernel

e4_data P498 F [1, 1, 1, 1] 498
theorem ok498 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 498 [])) P498.sel P498.B = true := by
  decide +kernel

e4_data P499 F [1, 1, 1, 1] 499
theorem ok499 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 499 [])) P499.sel P499.B = true := by
  decide +kernel

e4_data P500 F [1, 1, 1, 1] 500
theorem ok500 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 500 [])) P500.sel P500.B = true := by
  decide +kernel

e4_data P501 F [1, 1, 1, 1] 501
theorem ok501 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 501 [])) P501.sel P501.B = true := by
  decide +kernel

e4_data P502 F [1, 1, 1, 1] 502
theorem ok502 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 502 [])) P502.sel P502.B = true := by
  decide +kernel

e4_data P503 F [1, 1, 1, 1] 503
theorem ok503 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 503 [])) P503.sel P503.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
