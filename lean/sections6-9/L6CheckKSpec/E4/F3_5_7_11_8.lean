import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 64–71. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P64 F [3, 5, 7, 11] 64
theorem ok64 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 64 [])) P64.sel P64.B = true := by
  decide +kernel

e4_data P65 F [3, 5, 7, 11] 65
theorem ok65 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 65 [])) P65.sel P65.B = true := by
  decide +kernel

e4_data P66 F [3, 5, 7, 11] 66
theorem ok66 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 66 [])) P66.sel P66.B = true := by
  decide +kernel

e4_data P67 F [3, 5, 7, 11] 67
theorem ok67 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 67 [])) P67.sel P67.B = true := by
  decide +kernel

e4_data P68 F [3, 5, 7, 11] 68
theorem ok68 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 68 [])) P68.sel P68.B = true := by
  decide +kernel

e4_data P69 F [3, 5, 7, 11] 69
theorem ok69 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 69 [])) P69.sel P69.B = true := by
  decide +kernel

e4_data P70 F [3, 5, 7, 11] 70
theorem ok70 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 70 [])) P70.sel P70.B = true := by
  decide +kernel

e4_data P71 F [3, 5, 7, 11] 71
theorem ok71 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 71 [])) P71.sel P71.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
