import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 472–479. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P472 F [1, 1, 1, 1] 472
theorem ok472 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 472 [])) P472.sel P472.B = true := by
  decide +kernel

e4_data P473 F [1, 1, 1, 1] 473
theorem ok473 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 473 [])) P473.sel P473.B = true := by
  decide +kernel

e4_data P474 F [1, 1, 1, 1] 474
theorem ok474 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 474 [])) P474.sel P474.B = true := by
  decide +kernel

e4_data P475 F [1, 1, 1, 1] 475
theorem ok475 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 475 [])) P475.sel P475.B = true := by
  decide +kernel

e4_data P476 F [1, 1, 1, 1] 476
theorem ok476 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 476 [])) P476.sel P476.B = true := by
  decide +kernel

e4_data P477 F [1, 1, 1, 1] 477
theorem ok477 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 477 [])) P477.sel P477.B = true := by
  decide +kernel

e4_data P478 F [1, 1, 1, 1] 478
theorem ok478 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 478 [])) P478.sel P478.B = true := by
  decide +kernel

e4_data P479 F [1, 1, 1, 1] 479
theorem ok479 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 479 [])) P479.sel P479.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
