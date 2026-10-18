import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 152–159. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P152 F [1, 1, 1, 1] 152
theorem ok152 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 152 [])) P152.sel P152.B = true := by
  decide +kernel

e4_data P153 F [1, 1, 1, 1] 153
theorem ok153 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 153 [])) P153.sel P153.B = true := by
  decide +kernel

e4_data P154 F [1, 1, 1, 1] 154
theorem ok154 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 154 [])) P154.sel P154.B = true := by
  decide +kernel

e4_data P155 F [1, 1, 1, 1] 155
theorem ok155 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 155 [])) P155.sel P155.B = true := by
  decide +kernel

e4_data P156 F [1, 1, 1, 1] 156
theorem ok156 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 156 [])) P156.sel P156.B = true := by
  decide +kernel

e4_data P157 F [1, 1, 1, 1] 157
theorem ok157 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 157 [])) P157.sel P157.B = true := by
  decide +kernel

e4_data P158 F [1, 1, 1, 1] 158
theorem ok158 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 158 [])) P158.sel P158.B = true := by
  decide +kernel

e4_data P159 F [1, 1, 1, 1] 159
theorem ok159 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 159 [])) P159.sel P159.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
