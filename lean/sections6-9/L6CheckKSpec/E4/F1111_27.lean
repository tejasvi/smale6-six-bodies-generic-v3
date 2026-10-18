import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 216–223. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P216 F [1, 1, 1, 1] 216
theorem ok216 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 216 [])) P216.sel P216.B = true := by
  decide +kernel

e4_data P217 F [1, 1, 1, 1] 217
theorem ok217 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 217 [])) P217.sel P217.B = true := by
  decide +kernel

e4_data P218 F [1, 1, 1, 1] 218
theorem ok218 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 218 [])) P218.sel P218.B = true := by
  decide +kernel

e4_data P219 F [1, 1, 1, 1] 219
theorem ok219 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 219 [])) P219.sel P219.B = true := by
  decide +kernel

e4_data P220 F [1, 1, 1, 1] 220
theorem ok220 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 220 [])) P220.sel P220.B = true := by
  decide +kernel

e4_data P221 F [1, 1, 1, 1] 221
theorem ok221 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 221 [])) P221.sel P221.B = true := by
  decide +kernel

e4_data P222 F [1, 1, 1, 1] 222
theorem ok222 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 222 [])) P222.sel P222.B = true := by
  decide +kernel

e4_data P223 F [1, 1, 1, 1] 223
theorem ok223 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 223 [])) P223.sel P223.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
