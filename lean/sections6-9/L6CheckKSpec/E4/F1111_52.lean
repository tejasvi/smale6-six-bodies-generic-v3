import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 416–423. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P416 F [1, 1, 1, 1] 416
theorem ok416 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 416 [])) P416.sel P416.B = true := by
  decide +kernel

e4_data P417 F [1, 1, 1, 1] 417
theorem ok417 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 417 [])) P417.sel P417.B = true := by
  decide +kernel

e4_data P418 F [1, 1, 1, 1] 418
theorem ok418 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 418 [])) P418.sel P418.B = true := by
  decide +kernel

e4_data P419 F [1, 1, 1, 1] 419
theorem ok419 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 419 [])) P419.sel P419.B = true := by
  decide +kernel

e4_data P420 F [1, 1, 1, 1] 420
theorem ok420 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 420 [])) P420.sel P420.B = true := by
  decide +kernel

e4_data P421 F [1, 1, 1, 1] 421
theorem ok421 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 421 [])) P421.sel P421.B = true := by
  decide +kernel

e4_data P422 F [1, 1, 1, 1] 422
theorem ok422 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 422 [])) P422.sel P422.B = true := by
  decide +kernel

e4_data P423 F [1, 1, 1, 1] 423
theorem ok423 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 423 [])) P423.sel P423.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
