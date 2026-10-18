import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 728–728. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P728 F [3, 5, 7, 11] 728
theorem ok728 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 728 [])) P728.sel P728.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
