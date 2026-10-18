import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 104–111. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P104 F [1, 1, 1, 1] 104
theorem ok104 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 104 [])) P104.sel P104.B = true := by
  decide +kernel

e4_data P105 F [1, 1, 1, 1] 105
theorem ok105 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 105 [])) P105.sel P105.B = true := by
  decide +kernel

e4_data P106 F [1, 1, 1, 1] 106
theorem ok106 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 106 [])) P106.sel P106.B = true := by
  decide +kernel

e4_data P107 F [1, 1, 1, 1] 107
theorem ok107 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 107 [])) P107.sel P107.B = true := by
  decide +kernel

e4_data P108 F [1, 1, 1, 1] 108
theorem ok108 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 108 [])) P108.sel P108.B = true := by
  decide +kernel

e4_data P109 F [1, 1, 1, 1] 109
theorem ok109 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 109 [])) P109.sel P109.B = true := by
  decide +kernel

e4_data P110 F [1, 1, 1, 1] 110
theorem ok110 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 110 [])) P110.sel P110.B = true := by
  decide +kernel

e4_data P111 F [1, 1, 1, 1] 111
theorem ok111 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 111 [])) P111.sel P111.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
