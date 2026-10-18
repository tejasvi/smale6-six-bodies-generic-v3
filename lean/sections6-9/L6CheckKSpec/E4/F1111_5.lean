import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 40–47. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P40 F [1, 1, 1, 1] 40
theorem ok40 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 40 [])) P40.sel P40.B = true := by
  decide +kernel

e4_data P41 F [1, 1, 1, 1] 41
theorem ok41 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 41 [])) P41.sel P41.B = true := by
  decide +kernel

e4_data P42 F [1, 1, 1, 1] 42
theorem ok42 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 42 [])) P42.sel P42.B = true := by
  decide +kernel

e4_data P43 F [1, 1, 1, 1] 43
theorem ok43 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 43 [])) P43.sel P43.B = true := by
  decide +kernel

e4_data P44 F [1, 1, 1, 1] 44
theorem ok44 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 44 [])) P44.sel P44.B = true := by
  decide +kernel

e4_data P45 F [1, 1, 1, 1] 45
theorem ok45 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 45 [])) P45.sel P45.B = true := by
  decide +kernel

e4_data P46 F [1, 1, 1, 1] 46
theorem ok46 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 46 [])) P46.sel P46.B = true := by
  decide +kernel

e4_data P47 F [1, 1, 1, 1] 47
theorem ok47 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 47 [])) P47.sel P47.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
