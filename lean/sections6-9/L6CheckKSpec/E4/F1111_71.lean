import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 568–575. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P568 F [1, 1, 1, 1] 568
theorem ok568 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 568 [])) P568.sel P568.B = true := by
  decide +kernel

e4_data P569 F [1, 1, 1, 1] 569
theorem ok569 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 569 [])) P569.sel P569.B = true := by
  decide +kernel

e4_data P570 F [1, 1, 1, 1] 570
theorem ok570 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 570 [])) P570.sel P570.B = true := by
  decide +kernel

e4_data P571 F [1, 1, 1, 1] 571
theorem ok571 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 571 [])) P571.sel P571.B = true := by
  decide +kernel

e4_data P572 F [1, 1, 1, 1] 572
theorem ok572 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 572 [])) P572.sel P572.B = true := by
  decide +kernel

e4_data P573 F [1, 1, 1, 1] 573
theorem ok573 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 573 [])) P573.sel P573.B = true := by
  decide +kernel

e4_data P574 F [1, 1, 1, 1] 574
theorem ok574 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 574 [])) P574.sel P574.B = true := by
  decide +kernel

e4_data P575 F [1, 1, 1, 1] 575
theorem ok575 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 575 [])) P575.sel P575.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
