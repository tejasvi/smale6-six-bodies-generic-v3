import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 456–463. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P456 F [1, 1, 1, 1] 456
theorem ok456 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 456 [])) P456.sel P456.B = true := by
  decide +kernel

e4_data P457 F [1, 1, 1, 1] 457
theorem ok457 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 457 [])) P457.sel P457.B = true := by
  decide +kernel

e4_data P458 F [1, 1, 1, 1] 458
theorem ok458 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 458 [])) P458.sel P458.B = true := by
  decide +kernel

e4_data P459 F [1, 1, 1, 1] 459
theorem ok459 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 459 [])) P459.sel P459.B = true := by
  decide +kernel

e4_data P460 F [1, 1, 1, 1] 460
theorem ok460 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 460 [])) P460.sel P460.B = true := by
  decide +kernel

e4_data P461 F [1, 1, 1, 1] 461
theorem ok461 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 461 [])) P461.sel P461.B = true := by
  decide +kernel

e4_data P462 F [1, 1, 1, 1] 462
theorem ok462 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 462 [])) P462.sel P462.B = true := by
  decide +kernel

e4_data P463 F [1, 1, 1, 1] 463
theorem ok463 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 463 [])) P463.sel P463.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
