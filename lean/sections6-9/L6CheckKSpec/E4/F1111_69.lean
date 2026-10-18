import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 552–559. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P552 F [1, 1, 1, 1] 552
theorem ok552 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 552 [])) P552.sel P552.B = true := by
  decide +kernel

e4_data P553 F [1, 1, 1, 1] 553
theorem ok553 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 553 [])) P553.sel P553.B = true := by
  decide +kernel

e4_data P554 F [1, 1, 1, 1] 554
theorem ok554 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 554 [])) P554.sel P554.B = true := by
  decide +kernel

e4_data P555 F [1, 1, 1, 1] 555
theorem ok555 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 555 [])) P555.sel P555.B = true := by
  decide +kernel

e4_data P556 F [1, 1, 1, 1] 556
theorem ok556 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 556 [])) P556.sel P556.B = true := by
  decide +kernel

e4_data P557 F [1, 1, 1, 1] 557
theorem ok557 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 557 [])) P557.sel P557.B = true := by
  decide +kernel

e4_data P558 F [1, 1, 1, 1] 558
theorem ok558 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 558 [])) P558.sel P558.B = true := by
  decide +kernel

e4_data P559 F [1, 1, 1, 1] 559
theorem ok559 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 559 [])) P559.sel P559.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
