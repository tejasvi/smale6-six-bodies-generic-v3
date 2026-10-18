import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 120–127. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P120 F [1, 1, 1, 1] 120
theorem ok120 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 120 [])) P120.sel P120.B = true := by
  decide +kernel

e4_data P121 F [1, 1, 1, 1] 121
theorem ok121 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 121 [])) P121.sel P121.B = true := by
  decide +kernel

e4_data P122 F [1, 1, 1, 1] 122
theorem ok122 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 122 [])) P122.sel P122.B = true := by
  decide +kernel

e4_data P123 F [1, 1, 1, 1] 123
theorem ok123 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 123 [])) P123.sel P123.B = true := by
  decide +kernel

e4_data P124 F [1, 1, 1, 1] 124
theorem ok124 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 124 [])) P124.sel P124.B = true := by
  decide +kernel

e4_data P125 F [1, 1, 1, 1] 125
theorem ok125 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 125 [])) P125.sel P125.B = true := by
  decide +kernel

e4_data P126 F [1, 1, 1, 1] 126
theorem ok126 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 126 [])) P126.sel P126.B = true := by
  decide +kernel

e4_data P127 F [1, 1, 1, 1] 127
theorem ok127 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 127 [])) P127.sel P127.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
