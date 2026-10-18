import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 208–215. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P208 F [1, 1, 1, 1] 208
theorem ok208 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 208 [])) P208.sel P208.B = true := by
  decide +kernel

e4_data P209 F [1, 1, 1, 1] 209
theorem ok209 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 209 [])) P209.sel P209.B = true := by
  decide +kernel

e4_data P210 F [1, 1, 1, 1] 210
theorem ok210 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 210 [])) P210.sel P210.B = true := by
  decide +kernel

e4_data P211 F [1, 1, 1, 1] 211
theorem ok211 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 211 [])) P211.sel P211.B = true := by
  decide +kernel

e4_data P212 F [1, 1, 1, 1] 212
theorem ok212 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 212 [])) P212.sel P212.B = true := by
  decide +kernel

e4_data P213 F [1, 1, 1, 1] 213
theorem ok213 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 213 [])) P213.sel P213.B = true := by
  decide +kernel

e4_data P214 F [1, 1, 1, 1] 214
theorem ok214 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 214 [])) P214.sel P214.B = true := by
  decide +kernel

e4_data P215 F [1, 1, 1, 1] 215
theorem ok215 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 215 [])) P215.sel P215.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
