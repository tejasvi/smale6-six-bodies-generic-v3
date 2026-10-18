import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 192–199. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P192 F [1, 1, 1, 1] 192
theorem ok192 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 192 [])) P192.sel P192.B = true := by
  decide +kernel

e4_data P193 F [1, 1, 1, 1] 193
theorem ok193 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 193 [])) P193.sel P193.B = true := by
  decide +kernel

e4_data P194 F [1, 1, 1, 1] 194
theorem ok194 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 194 [])) P194.sel P194.B = true := by
  decide +kernel

e4_data P195 F [1, 1, 1, 1] 195
theorem ok195 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 195 [])) P195.sel P195.B = true := by
  decide +kernel

e4_data P196 F [1, 1, 1, 1] 196
theorem ok196 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 196 [])) P196.sel P196.B = true := by
  decide +kernel

e4_data P197 F [1, 1, 1, 1] 197
theorem ok197 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 197 [])) P197.sel P197.B = true := by
  decide +kernel

e4_data P198 F [1, 1, 1, 1] 198
theorem ok198 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 198 [])) P198.sel P198.B = true := by
  decide +kernel

e4_data P199 F [1, 1, 1, 1] 199
theorem ok199 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 199 [])) P199.sel P199.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
