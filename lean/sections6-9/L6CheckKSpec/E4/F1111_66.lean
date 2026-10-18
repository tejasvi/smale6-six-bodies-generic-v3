import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 528–535. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P528 F [1, 1, 1, 1] 528
theorem ok528 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 528 [])) P528.sel P528.B = true := by
  decide +kernel

e4_data P529 F [1, 1, 1, 1] 529
theorem ok529 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 529 [])) P529.sel P529.B = true := by
  decide +kernel

e4_data P530 F [1, 1, 1, 1] 530
theorem ok530 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 530 [])) P530.sel P530.B = true := by
  decide +kernel

e4_data P531 F [1, 1, 1, 1] 531
theorem ok531 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 531 [])) P531.sel P531.B = true := by
  decide +kernel

e4_data P532 F [1, 1, 1, 1] 532
theorem ok532 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 532 [])) P532.sel P532.B = true := by
  decide +kernel

e4_data P533 F [1, 1, 1, 1] 533
theorem ok533 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 533 [])) P533.sel P533.B = true := by
  decide +kernel

e4_data P534 F [1, 1, 1, 1] 534
theorem ok534 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 534 [])) P534.sel P534.B = true := by
  decide +kernel

e4_data P535 F [1, 1, 1, 1] 535
theorem ok535 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 535 [])) P535.sel P535.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
