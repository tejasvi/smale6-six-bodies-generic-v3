import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 32–39. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P32 F [1, 1, 1, 1] 32
theorem ok32 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 32 [])) P32.sel P32.B = true := by
  decide +kernel

e4_data P33 F [1, 1, 1, 1] 33
theorem ok33 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 33 [])) P33.sel P33.B = true := by
  decide +kernel

e4_data P34 F [1, 1, 1, 1] 34
theorem ok34 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 34 [])) P34.sel P34.B = true := by
  decide +kernel

e4_data P35 F [1, 1, 1, 1] 35
theorem ok35 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 35 [])) P35.sel P35.B = true := by
  decide +kernel

e4_data P36 F [1, 1, 1, 1] 36
theorem ok36 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 36 [])) P36.sel P36.B = true := by
  decide +kernel

e4_data P37 F [1, 1, 1, 1] 37
theorem ok37 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 37 [])) P37.sel P37.B = true := by
  decide +kernel

e4_data P38 F [1, 1, 1, 1] 38
theorem ok38 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 38 [])) P38.sel P38.B = true := by
  decide +kernel

e4_data P39 F [1, 1, 1, 1] 39
theorem ok39 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 39 [])) P39.sel P39.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
