import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 336–343. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P336 F [3, 5, 7, 11] 336
theorem ok336 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 336 [])) P336.sel P336.B = true := by
  decide +kernel

e4_data P337 F [3, 5, 7, 11] 337
theorem ok337 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 337 [])) P337.sel P337.B = true := by
  decide +kernel

e4_data P338 F [3, 5, 7, 11] 338
theorem ok338 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 338 [])) P338.sel P338.B = true := by
  decide +kernel

e4_data P339 F [3, 5, 7, 11] 339
theorem ok339 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 339 [])) P339.sel P339.B = true := by
  decide +kernel

e4_data P340 F [3, 5, 7, 11] 340
theorem ok340 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 340 [])) P340.sel P340.B = true := by
  decide +kernel

e4_data P341 F [3, 5, 7, 11] 341
theorem ok341 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 341 [])) P341.sel P341.B = true := by
  decide +kernel

e4_data P342 F [3, 5, 7, 11] 342
theorem ok342 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 342 [])) P342.sel P342.B = true := by
  decide +kernel

e4_data P343 F [3, 5, 7, 11] 343
theorem ok343 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 343 [])) P343.sel P343.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
