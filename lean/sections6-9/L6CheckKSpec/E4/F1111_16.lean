import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 128–135. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P128 F [1, 1, 1, 1] 128
theorem ok128 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 128 [])) P128.sel P128.B = true := by
  decide +kernel

e4_data P129 F [1, 1, 1, 1] 129
theorem ok129 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 129 [])) P129.sel P129.B = true := by
  decide +kernel

e4_data P130 F [1, 1, 1, 1] 130
theorem ok130 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 130 [])) P130.sel P130.B = true := by
  decide +kernel

e4_data P131 F [1, 1, 1, 1] 131
theorem ok131 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 131 [])) P131.sel P131.B = true := by
  decide +kernel

e4_data P132 F [1, 1, 1, 1] 132
theorem ok132 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 132 [])) P132.sel P132.B = true := by
  decide +kernel

e4_data P133 F [1, 1, 1, 1] 133
theorem ok133 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 133 [])) P133.sel P133.B = true := by
  decide +kernel

e4_data P134 F [1, 1, 1, 1] 134
theorem ok134 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 134 [])) P134.sel P134.B = true := by
  decide +kernel

e4_data P135 F [1, 1, 1, 1] 135
theorem ok135 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 135 [])) P135.sel P135.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
