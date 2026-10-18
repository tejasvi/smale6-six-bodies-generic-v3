import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 176–183. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P176 F [3, 5, 7, 11] 176
theorem ok176 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 176 [])) P176.sel P176.B = true := by
  decide +kernel

e4_data P177 F [3, 5, 7, 11] 177
theorem ok177 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 177 [])) P177.sel P177.B = true := by
  decide +kernel

e4_data P178 F [3, 5, 7, 11] 178
theorem ok178 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 178 [])) P178.sel P178.B = true := by
  decide +kernel

e4_data P179 F [3, 5, 7, 11] 179
theorem ok179 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 179 [])) P179.sel P179.B = true := by
  decide +kernel

e4_data P180 F [3, 5, 7, 11] 180
theorem ok180 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 180 [])) P180.sel P180.B = true := by
  decide +kernel

e4_data P181 F [3, 5, 7, 11] 181
theorem ok181 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 181 [])) P181.sel P181.B = true := by
  decide +kernel

e4_data P182 F [3, 5, 7, 11] 182
theorem ok182 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 182 [])) P182.sel P182.B = true := by
  decide +kernel

e4_data P183 F [3, 5, 7, 11] 183
theorem ok183 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 183 [])) P183.sel P183.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
