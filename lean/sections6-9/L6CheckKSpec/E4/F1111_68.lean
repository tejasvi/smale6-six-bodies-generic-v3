import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 544–551. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P544 F [1, 1, 1, 1] 544
theorem ok544 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 544 [])) P544.sel P544.B = true := by
  decide +kernel

e4_data P545 F [1, 1, 1, 1] 545
theorem ok545 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 545 [])) P545.sel P545.B = true := by
  decide +kernel

e4_data P546 F [1, 1, 1, 1] 546
theorem ok546 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 546 [])) P546.sel P546.B = true := by
  decide +kernel

e4_data P547 F [1, 1, 1, 1] 547
theorem ok547 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 547 [])) P547.sel P547.B = true := by
  decide +kernel

e4_data P548 F [1, 1, 1, 1] 548
theorem ok548 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 548 [])) P548.sel P548.B = true := by
  decide +kernel

e4_data P549 F [1, 1, 1, 1] 549
theorem ok549 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 549 [])) P549.sel P549.B = true := by
  decide +kernel

e4_data P550 F [1, 1, 1, 1] 550
theorem ok550 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 550 [])) P550.sel P550.B = true := by
  decide +kernel

e4_data P551 F [1, 1, 1, 1] 551
theorem ok551 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 551 [])) P551.sel P551.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
