import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 272–279. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P272 F [3, 5, 7, 11] 272
theorem ok272 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 272 [])) P272.sel P272.B = true := by
  decide +kernel

e4_data P273 F [3, 5, 7, 11] 273
theorem ok273 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 273 [])) P273.sel P273.B = true := by
  decide +kernel

e4_data P274 F [3, 5, 7, 11] 274
theorem ok274 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 274 [])) P274.sel P274.B = true := by
  decide +kernel

e4_data P275 F [3, 5, 7, 11] 275
theorem ok275 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 275 [])) P275.sel P275.B = true := by
  decide +kernel

e4_data P276 F [3, 5, 7, 11] 276
theorem ok276 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 276 [])) P276.sel P276.B = true := by
  decide +kernel

e4_data P277 F [3, 5, 7, 11] 277
theorem ok277 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 277 [])) P277.sel P277.B = true := by
  decide +kernel

e4_data P278 F [3, 5, 7, 11] 278
theorem ok278 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 278 [])) P278.sel P278.B = true := by
  decide +kernel

e4_data P279 F [3, 5, 7, 11] 279
theorem ok279 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 279 [])) P279.sel P279.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
