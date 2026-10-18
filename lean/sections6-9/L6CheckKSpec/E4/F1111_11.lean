import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 88–95. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P88 F [1, 1, 1, 1] 88
theorem ok88 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 88 [])) P88.sel P88.B = true := by
  decide +kernel

e4_data P89 F [1, 1, 1, 1] 89
theorem ok89 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 89 [])) P89.sel P89.B = true := by
  decide +kernel

e4_data P90 F [1, 1, 1, 1] 90
theorem ok90 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 90 [])) P90.sel P90.B = true := by
  decide +kernel

e4_data P91 F [1, 1, 1, 1] 91
theorem ok91 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 91 [])) P91.sel P91.B = true := by
  decide +kernel

e4_data P92 F [1, 1, 1, 1] 92
theorem ok92 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 92 [])) P92.sel P92.B = true := by
  decide +kernel

e4_data P93 F [1, 1, 1, 1] 93
theorem ok93 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 93 [])) P93.sel P93.B = true := by
  decide +kernel

e4_data P94 F [1, 1, 1, 1] 94
theorem ok94 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 94 [])) P94.sel P94.B = true := by
  decide +kernel

e4_data P95 F [1, 1, 1, 1] 95
theorem ok95 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 95 [])) P95.sel P95.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
