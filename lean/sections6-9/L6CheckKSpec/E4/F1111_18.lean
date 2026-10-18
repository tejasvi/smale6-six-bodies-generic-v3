import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 144–151. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P144 F [1, 1, 1, 1] 144
theorem ok144 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 144 [])) P144.sel P144.B = true := by
  decide +kernel

e4_data P145 F [1, 1, 1, 1] 145
theorem ok145 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 145 [])) P145.sel P145.B = true := by
  decide +kernel

e4_data P146 F [1, 1, 1, 1] 146
theorem ok146 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 146 [])) P146.sel P146.B = true := by
  decide +kernel

e4_data P147 F [1, 1, 1, 1] 147
theorem ok147 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 147 [])) P147.sel P147.B = true := by
  decide +kernel

e4_data P148 F [1, 1, 1, 1] 148
theorem ok148 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 148 [])) P148.sel P148.B = true := by
  decide +kernel

e4_data P149 F [1, 1, 1, 1] 149
theorem ok149 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 149 [])) P149.sel P149.B = true := by
  decide +kernel

e4_data P150 F [1, 1, 1, 1] 150
theorem ok150 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 150 [])) P150.sel P150.B = true := by
  decide +kernel

e4_data P151 F [1, 1, 1, 1] 151
theorem ok151 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 151 [])) P151.sel P151.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
