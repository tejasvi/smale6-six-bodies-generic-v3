import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 176–183. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P176 F [1, 1, 1, 1] 176
theorem ok176 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 176 [])) P176.sel P176.B = true := by
  decide +kernel

e4_data P177 F [1, 1, 1, 1] 177
theorem ok177 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 177 [])) P177.sel P177.B = true := by
  decide +kernel

e4_data P178 F [1, 1, 1, 1] 178
theorem ok178 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 178 [])) P178.sel P178.B = true := by
  decide +kernel

e4_data P179 F [1, 1, 1, 1] 179
theorem ok179 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 179 [])) P179.sel P179.B = true := by
  decide +kernel

e4_data P180 F [1, 1, 1, 1] 180
theorem ok180 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 180 [])) P180.sel P180.B = true := by
  decide +kernel

e4_data P181 F [1, 1, 1, 1] 181
theorem ok181 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 181 [])) P181.sel P181.B = true := by
  decide +kernel

e4_data P182 F [1, 1, 1, 1] 182
theorem ok182 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 182 [])) P182.sel P182.B = true := by
  decide +kernel

e4_data P183 F [1, 1, 1, 1] 183
theorem ok183 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 183 [])) P183.sel P183.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
