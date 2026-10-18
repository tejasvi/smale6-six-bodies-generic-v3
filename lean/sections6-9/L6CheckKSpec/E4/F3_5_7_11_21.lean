import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 168–175. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P168 F [3, 5, 7, 11] 168
theorem ok168 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 168 [])) P168.sel P168.B = true := by
  decide +kernel

e4_data P169 F [3, 5, 7, 11] 169
theorem ok169 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 169 [])) P169.sel P169.B = true := by
  decide +kernel

e4_data P170 F [3, 5, 7, 11] 170
theorem ok170 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 170 [])) P170.sel P170.B = true := by
  decide +kernel

e4_data P171 F [3, 5, 7, 11] 171
theorem ok171 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 171 [])) P171.sel P171.B = true := by
  decide +kernel

e4_data P172 F [3, 5, 7, 11] 172
theorem ok172 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 172 [])) P172.sel P172.B = true := by
  decide +kernel

e4_data P173 F [3, 5, 7, 11] 173
theorem ok173 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 173 [])) P173.sel P173.B = true := by
  decide +kernel

e4_data P174 F [3, 5, 7, 11] 174
theorem ok174 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 174 [])) P174.sel P174.B = true := by
  decide +kernel

e4_data P175 F [3, 5, 7, 11] 175
theorem ok175 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 175 [])) P175.sel P175.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
