import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 128–135. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P128 F [3, 5, 7, 11] 128
theorem ok128 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 128 [])) P128.sel P128.B = true := by
  decide +kernel

e4_data P129 F [3, 5, 7, 11] 129
theorem ok129 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 129 [])) P129.sel P129.B = true := by
  decide +kernel

e4_data P130 F [3, 5, 7, 11] 130
theorem ok130 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 130 [])) P130.sel P130.B = true := by
  decide +kernel

e4_data P131 F [3, 5, 7, 11] 131
theorem ok131 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 131 [])) P131.sel P131.B = true := by
  decide +kernel

e4_data P132 F [3, 5, 7, 11] 132
theorem ok132 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 132 [])) P132.sel P132.B = true := by
  decide +kernel

e4_data P133 F [3, 5, 7, 11] 133
theorem ok133 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 133 [])) P133.sel P133.B = true := by
  decide +kernel

e4_data P134 F [3, 5, 7, 11] 134
theorem ok134 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 134 [])) P134.sel P134.B = true := by
  decide +kernel

e4_data P135 F [3, 5, 7, 11] 135
theorem ok135 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 135 [])) P135.sel P135.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
