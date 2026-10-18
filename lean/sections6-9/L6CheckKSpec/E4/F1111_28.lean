import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 224–231. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P224 F [1, 1, 1, 1] 224
theorem ok224 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 224 [])) P224.sel P224.B = true := by
  decide +kernel

e4_data P225 F [1, 1, 1, 1] 225
theorem ok225 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 225 [])) P225.sel P225.B = true := by
  decide +kernel

e4_data P226 F [1, 1, 1, 1] 226
theorem ok226 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 226 [])) P226.sel P226.B = true := by
  decide +kernel

e4_data P227 F [1, 1, 1, 1] 227
theorem ok227 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 227 [])) P227.sel P227.B = true := by
  decide +kernel

e4_data P228 F [1, 1, 1, 1] 228
theorem ok228 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 228 [])) P228.sel P228.B = true := by
  decide +kernel

e4_data P229 F [1, 1, 1, 1] 229
theorem ok229 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 229 [])) P229.sel P229.B = true := by
  decide +kernel

e4_data P230 F [1, 1, 1, 1] 230
theorem ok230 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 230 [])) P230.sel P230.B = true := by
  decide +kernel

e4_data P231 F [1, 1, 1, 1] 231
theorem ok231 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 231 [])) P231.sel P231.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
