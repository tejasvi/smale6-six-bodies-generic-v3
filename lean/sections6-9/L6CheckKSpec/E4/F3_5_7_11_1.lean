import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 8–15. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P8 F [3, 5, 7, 11] 8
theorem ok8 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 8 [])) P8.sel P8.B = true := by
  decide +kernel

e4_data P9 F [3, 5, 7, 11] 9
theorem ok9 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 9 [])) P9.sel P9.B = true := by
  decide +kernel

e4_data P10 F [3, 5, 7, 11] 10
theorem ok10 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 10 [])) P10.sel P10.B = true := by
  decide +kernel

e4_data P11 F [3, 5, 7, 11] 11
theorem ok11 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 11 [])) P11.sel P11.B = true := by
  decide +kernel

e4_data P12 F [3, 5, 7, 11] 12
theorem ok12 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 12 [])) P12.sel P12.B = true := by
  decide +kernel

e4_data P13 F [3, 5, 7, 11] 13
theorem ok13 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 13 [])) P13.sel P13.B = true := by
  decide +kernel

e4_data P14 F [3, 5, 7, 11] 14
theorem ok14 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 14 [])) P14.sel P14.B = true := by
  decide +kernel

e4_data P15 F [3, 5, 7, 11] 15
theorem ok15 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 15 [])) P15.sel P15.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
