import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 136–143. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P136 F [1, 1, 1, 1] 136
theorem ok136 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 136 [])) P136.sel P136.B = true := by
  decide +kernel

e4_data P137 F [1, 1, 1, 1] 137
theorem ok137 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 137 [])) P137.sel P137.B = true := by
  decide +kernel

e4_data P138 F [1, 1, 1, 1] 138
theorem ok138 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 138 [])) P138.sel P138.B = true := by
  decide +kernel

e4_data P139 F [1, 1, 1, 1] 139
theorem ok139 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 139 [])) P139.sel P139.B = true := by
  decide +kernel

e4_data P140 F [1, 1, 1, 1] 140
theorem ok140 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 140 [])) P140.sel P140.B = true := by
  decide +kernel

e4_data P141 F [1, 1, 1, 1] 141
theorem ok141 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 141 [])) P141.sel P141.B = true := by
  decide +kernel

e4_data P142 F [1, 1, 1, 1] 142
theorem ok142 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 142 [])) P142.sel P142.B = true := by
  decide +kernel

e4_data P143 F [1, 1, 1, 1] 143
theorem ok143 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 143 [])) P143.sel P143.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
