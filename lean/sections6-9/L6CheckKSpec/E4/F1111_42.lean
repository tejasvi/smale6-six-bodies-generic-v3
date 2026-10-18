import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 336–343. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P336 F [1, 1, 1, 1] 336
theorem ok336 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 336 [])) P336.sel P336.B = true := by
  decide +kernel

e4_data P337 F [1, 1, 1, 1] 337
theorem ok337 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 337 [])) P337.sel P337.B = true := by
  decide +kernel

e4_data P338 F [1, 1, 1, 1] 338
theorem ok338 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 338 [])) P338.sel P338.B = true := by
  decide +kernel

e4_data P339 F [1, 1, 1, 1] 339
theorem ok339 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 339 [])) P339.sel P339.B = true := by
  decide +kernel

e4_data P340 F [1, 1, 1, 1] 340
theorem ok340 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 340 [])) P340.sel P340.B = true := by
  decide +kernel

e4_data P341 F [1, 1, 1, 1] 341
theorem ok341 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 341 [])) P341.sel P341.B = true := by
  decide +kernel

e4_data P342 F [1, 1, 1, 1] 342
theorem ok342 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 342 [])) P342.sel P342.B = true := by
  decide +kernel

e4_data P343 F [1, 1, 1, 1] 343
theorem ok343 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 343 [])) P343.sel P343.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
