import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 520–527. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P520 F [1, 1, 1, 1] 520
theorem ok520 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 520 [])) P520.sel P520.B = true := by
  decide +kernel

e4_data P521 F [1, 1, 1, 1] 521
theorem ok521 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 521 [])) P521.sel P521.B = true := by
  decide +kernel

e4_data P522 F [1, 1, 1, 1] 522
theorem ok522 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 522 [])) P522.sel P522.B = true := by
  decide +kernel

e4_data P523 F [1, 1, 1, 1] 523
theorem ok523 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 523 [])) P523.sel P523.B = true := by
  decide +kernel

e4_data P524 F [1, 1, 1, 1] 524
theorem ok524 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 524 [])) P524.sel P524.B = true := by
  decide +kernel

e4_data P525 F [1, 1, 1, 1] 525
theorem ok525 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 525 [])) P525.sel P525.B = true := by
  decide +kernel

e4_data P526 F [1, 1, 1, 1] 526
theorem ok526 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 526 [])) P526.sel P526.B = true := by
  decide +kernel

e4_data P527 F [1, 1, 1, 1] 527
theorem ok527 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 527 [])) P527.sel P527.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
