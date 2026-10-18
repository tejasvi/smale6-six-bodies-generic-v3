import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 56–63. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P56 F [3, 5, 7, 11] 56
theorem ok56 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 56 [])) P56.sel P56.B = true := by
  decide +kernel

e4_data P57 F [3, 5, 7, 11] 57
theorem ok57 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 57 [])) P57.sel P57.B = true := by
  decide +kernel

e4_data P58 F [3, 5, 7, 11] 58
theorem ok58 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 58 [])) P58.sel P58.B = true := by
  decide +kernel

e4_data P59 F [3, 5, 7, 11] 59
theorem ok59 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 59 [])) P59.sel P59.B = true := by
  decide +kernel

e4_data P60 F [3, 5, 7, 11] 60
theorem ok60 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 60 [])) P60.sel P60.B = true := by
  decide +kernel

e4_data P61 F [3, 5, 7, 11] 61
theorem ok61 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 61 [])) P61.sel P61.B = true := by
  decide +kernel

e4_data P62 F [3, 5, 7, 11] 62
theorem ok62 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 62 [])) P62.sel P62.B = true := by
  decide +kernel

e4_data P63 F [3, 5, 7, 11] 63
theorem ok63 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 63 [])) P63.sel P63.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
