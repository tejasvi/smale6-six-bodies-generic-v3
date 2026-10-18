import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 424–431. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P424 F [3, 5, 7, 11] 424
theorem ok424 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 424 [])) P424.sel P424.B = true := by
  decide +kernel

e4_data P425 F [3, 5, 7, 11] 425
theorem ok425 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 425 [])) P425.sel P425.B = true := by
  decide +kernel

e4_data P426 F [3, 5, 7, 11] 426
theorem ok426 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 426 [])) P426.sel P426.B = true := by
  decide +kernel

e4_data P427 F [3, 5, 7, 11] 427
theorem ok427 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 427 [])) P427.sel P427.B = true := by
  decide +kernel

e4_data P428 F [3, 5, 7, 11] 428
theorem ok428 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 428 [])) P428.sel P428.B = true := by
  decide +kernel

e4_data P429 F [3, 5, 7, 11] 429
theorem ok429 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 429 [])) P429.sel P429.B = true := by
  decide +kernel

e4_data P430 F [3, 5, 7, 11] 430
theorem ok430 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 430 [])) P430.sel P430.B = true := by
  decide +kernel

e4_data P431 F [3, 5, 7, 11] 431
theorem ok431 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 431 [])) P431.sel P431.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
