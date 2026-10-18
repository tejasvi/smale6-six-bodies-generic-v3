import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 296–303. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P296 F [1, 1, 1, 1] 296
theorem ok296 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 296 [])) P296.sel P296.B = true := by
  decide +kernel

e4_data P297 F [1, 1, 1, 1] 297
theorem ok297 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 297 [])) P297.sel P297.B = true := by
  decide +kernel

e4_data P298 F [1, 1, 1, 1] 298
theorem ok298 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 298 [])) P298.sel P298.B = true := by
  decide +kernel

e4_data P299 F [1, 1, 1, 1] 299
theorem ok299 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 299 [])) P299.sel P299.B = true := by
  decide +kernel

e4_data P300 F [1, 1, 1, 1] 300
theorem ok300 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 300 [])) P300.sel P300.B = true := by
  decide +kernel

e4_data P301 F [1, 1, 1, 1] 301
theorem ok301 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 301 [])) P301.sel P301.B = true := by
  decide +kernel

e4_data P302 F [1, 1, 1, 1] 302
theorem ok302 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 302 [])) P302.sel P302.B = true := by
  decide +kernel

e4_data P303 F [1, 1, 1, 1] 303
theorem ok303 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 303 [])) P303.sel P303.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
