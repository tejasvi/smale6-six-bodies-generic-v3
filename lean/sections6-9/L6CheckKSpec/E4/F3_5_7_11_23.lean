import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 184–191. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P184 F [3, 5, 7, 11] 184
theorem ok184 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 184 [])) P184.sel P184.B = true := by
  decide +kernel

e4_data P185 F [3, 5, 7, 11] 185
theorem ok185 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 185 [])) P185.sel P185.B = true := by
  decide +kernel

e4_data P186 F [3, 5, 7, 11] 186
theorem ok186 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 186 [])) P186.sel P186.B = true := by
  decide +kernel

e4_data P187 F [3, 5, 7, 11] 187
theorem ok187 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 187 [])) P187.sel P187.B = true := by
  decide +kernel

e4_data P188 F [3, 5, 7, 11] 188
theorem ok188 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 188 [])) P188.sel P188.B = true := by
  decide +kernel

e4_data P189 F [3, 5, 7, 11] 189
theorem ok189 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 189 [])) P189.sel P189.B = true := by
  decide +kernel

e4_data P190 F [3, 5, 7, 11] 190
theorem ok190 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 190 [])) P190.sel P190.B = true := by
  decide +kernel

e4_data P191 F [3, 5, 7, 11] 191
theorem ok191 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 191 [])) P191.sel P191.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
