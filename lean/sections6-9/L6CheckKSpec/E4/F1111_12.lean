import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 96–103. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P96 F [1, 1, 1, 1] 96
theorem ok96 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 96 [])) P96.sel P96.B = true := by
  decide +kernel

e4_data P97 F [1, 1, 1, 1] 97
theorem ok97 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 97 [])) P97.sel P97.B = true := by
  decide +kernel

e4_data P98 F [1, 1, 1, 1] 98
theorem ok98 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 98 [])) P98.sel P98.B = true := by
  decide +kernel

e4_data P99 F [1, 1, 1, 1] 99
theorem ok99 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 99 [])) P99.sel P99.B = true := by
  decide +kernel

e4_data P100 F [1, 1, 1, 1] 100
theorem ok100 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 100 [])) P100.sel P100.B = true := by
  decide +kernel

e4_data P101 F [1, 1, 1, 1] 101
theorem ok101 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 101 [])) P101.sel P101.B = true := by
  decide +kernel

e4_data P102 F [1, 1, 1, 1] 102
theorem ok102 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 102 [])) P102.sel P102.B = true := by
  decide +kernel

e4_data P103 F [1, 1, 1, 1] 103
theorem ok103 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 103 [])) P103.sel P103.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
