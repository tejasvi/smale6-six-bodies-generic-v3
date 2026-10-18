import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 16–23. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P16 F [3, 5, 7, 11] 16
theorem ok16 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 16 [])) P16.sel P16.B = true := by
  decide +kernel

e4_data P17 F [3, 5, 7, 11] 17
theorem ok17 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 17 [])) P17.sel P17.B = true := by
  decide +kernel

e4_data P18 F [3, 5, 7, 11] 18
theorem ok18 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 18 [])) P18.sel P18.B = true := by
  decide +kernel

e4_data P19 F [3, 5, 7, 11] 19
theorem ok19 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 19 [])) P19.sel P19.B = true := by
  decide +kernel

e4_data P20 F [3, 5, 7, 11] 20
theorem ok20 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 20 [])) P20.sel P20.B = true := by
  decide +kernel

e4_data P21 F [3, 5, 7, 11] 21
theorem ok21 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 21 [])) P21.sel P21.B = true := by
  decide +kernel

e4_data P22 F [3, 5, 7, 11] 22
theorem ok22 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 22 [])) P22.sel P22.B = true := by
  decide +kernel

e4_data P23 F [3, 5, 7, 11] 23
theorem ok23 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 23 [])) P23.sel P23.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
