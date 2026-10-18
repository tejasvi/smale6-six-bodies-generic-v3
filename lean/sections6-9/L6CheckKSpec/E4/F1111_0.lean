import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 0–7. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P0 F [1, 1, 1, 1] 0
theorem ok0 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 0 [])) P0.sel P0.B = true := by
  decide +kernel

e4_data P1 F [1, 1, 1, 1] 1
theorem ok1 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 1 [])) P1.sel P1.B = true := by
  decide +kernel

e4_data P2 F [1, 1, 1, 1] 2
theorem ok2 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 2 [])) P2.sel P2.B = true := by
  decide +kernel

e4_data P3 F [1, 1, 1, 1] 3
theorem ok3 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 3 [])) P3.sel P3.B = true := by
  decide +kernel

e4_data P4 F [1, 1, 1, 1] 4
theorem ok4 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 4 [])) P4.sel P4.B = true := by
  decide +kernel

e4_data P5 F [1, 1, 1, 1] 5
theorem ok5 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 5 [])) P5.sel P5.B = true := by
  decide +kernel

e4_data P6 F [1, 1, 1, 1] 6
theorem ok6 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 6 [])) P6.sel P6.B = true := by
  decide +kernel

e4_data P7 F [1, 1, 1, 1] 7
theorem ok7 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 7 [])) P7.sel P7.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
