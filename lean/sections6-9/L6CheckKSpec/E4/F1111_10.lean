import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 80–87. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P80 F [1, 1, 1, 1] 80
theorem ok80 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 80 [])) P80.sel P80.B = true := by
  decide +kernel

e4_data P81 F [1, 1, 1, 1] 81
theorem ok81 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 81 [])) P81.sel P81.B = true := by
  decide +kernel

e4_data P82 F [1, 1, 1, 1] 82
theorem ok82 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 82 [])) P82.sel P82.B = true := by
  decide +kernel

e4_data P83 F [1, 1, 1, 1] 83
theorem ok83 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 83 [])) P83.sel P83.B = true := by
  decide +kernel

e4_data P84 F [1, 1, 1, 1] 84
theorem ok84 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 84 [])) P84.sel P84.B = true := by
  decide +kernel

e4_data P85 F [1, 1, 1, 1] 85
theorem ok85 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 85 [])) P85.sel P85.B = true := by
  decide +kernel

e4_data P86 F [1, 1, 1, 1] 86
theorem ok86 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 86 [])) P86.sel P86.B = true := by
  decide +kernel

e4_data P87 F [1, 1, 1, 1] 87
theorem ok87 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 87 [])) P87.sel P87.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
