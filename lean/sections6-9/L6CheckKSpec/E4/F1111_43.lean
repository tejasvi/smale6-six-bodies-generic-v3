import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 344–351. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P344 F [1, 1, 1, 1] 344
theorem ok344 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 344 [])) P344.sel P344.B = true := by
  decide +kernel

e4_data P345 F [1, 1, 1, 1] 345
theorem ok345 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 345 [])) P345.sel P345.B = true := by
  decide +kernel

e4_data P346 F [1, 1, 1, 1] 346
theorem ok346 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 346 [])) P346.sel P346.B = true := by
  decide +kernel

e4_data P347 F [1, 1, 1, 1] 347
theorem ok347 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 347 [])) P347.sel P347.B = true := by
  decide +kernel

e4_data P348 F [1, 1, 1, 1] 348
theorem ok348 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 348 [])) P348.sel P348.B = true := by
  decide +kernel

e4_data P349 F [1, 1, 1, 1] 349
theorem ok349 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 349 [])) P349.sel P349.B = true := by
  decide +kernel

e4_data P350 F [1, 1, 1, 1] 350
theorem ok350 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 350 [])) P350.sel P350.B = true := by
  decide +kernel

e4_data P351 F [1, 1, 1, 1] 351
theorem ok351 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 351 [])) P351.sel P351.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
