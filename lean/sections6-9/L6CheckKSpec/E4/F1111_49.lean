import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 392–399. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P392 F [1, 1, 1, 1] 392
theorem ok392 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 392 [])) P392.sel P392.B = true := by
  decide +kernel

e4_data P393 F [1, 1, 1, 1] 393
theorem ok393 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 393 [])) P393.sel P393.B = true := by
  decide +kernel

e4_data P394 F [1, 1, 1, 1] 394
theorem ok394 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 394 [])) P394.sel P394.B = true := by
  decide +kernel

e4_data P395 F [1, 1, 1, 1] 395
theorem ok395 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 395 [])) P395.sel P395.B = true := by
  decide +kernel

e4_data P396 F [1, 1, 1, 1] 396
theorem ok396 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 396 [])) P396.sel P396.B = true := by
  decide +kernel

e4_data P397 F [1, 1, 1, 1] 397
theorem ok397 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 397 [])) P397.sel P397.B = true := by
  decide +kernel

e4_data P398 F [1, 1, 1, 1] 398
theorem ok398 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 398 [])) P398.sel P398.B = true := by
  decide +kernel

e4_data P399 F [1, 1, 1, 1] 399
theorem ok399 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 399 [])) P399.sel P399.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
