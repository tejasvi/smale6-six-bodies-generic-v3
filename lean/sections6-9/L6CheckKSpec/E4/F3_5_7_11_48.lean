import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 384–391. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P384 F [3, 5, 7, 11] 384
theorem ok384 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 384 [])) P384.sel P384.B = true := by
  decide +kernel

e4_data P385 F [3, 5, 7, 11] 385
theorem ok385 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 385 [])) P385.sel P385.B = true := by
  decide +kernel

e4_data P386 F [3, 5, 7, 11] 386
theorem ok386 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 386 [])) P386.sel P386.B = true := by
  decide +kernel

e4_data P387 F [3, 5, 7, 11] 387
theorem ok387 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 387 [])) P387.sel P387.B = true := by
  decide +kernel

e4_data P388 F [3, 5, 7, 11] 388
theorem ok388 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 388 [])) P388.sel P388.B = true := by
  decide +kernel

e4_data P389 F [3, 5, 7, 11] 389
theorem ok389 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 389 [])) P389.sel P389.B = true := by
  decide +kernel

e4_data P390 F [3, 5, 7, 11] 390
theorem ok390 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 390 [])) P390.sel P390.B = true := by
  decide +kernel

e4_data P391 F [3, 5, 7, 11] 391
theorem ok391 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 391 [])) P391.sel P391.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
