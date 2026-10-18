import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `G` at `μ = (3, 5, 7, 11)`, patterns 32–39. -/

namespace L6CheckKSpec.E4.G3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P32 G [3, 5, 7, 11] 32
theorem ok32 : macCheckK 3 8 pE sE (formsGK [3, 5, 7, 11] (patsG.getD 32 [])) P32.sel P32.B = true := by
  decide +kernel

e4_data P33 G [3, 5, 7, 11] 33
theorem ok33 : macCheckK 3 8 pE sE (formsGK [3, 5, 7, 11] (patsG.getD 33 [])) P33.sel P33.B = true := by
  decide +kernel

e4_data P34 G [3, 5, 7, 11] 34
theorem ok34 : macCheckK 3 8 pE sE (formsGK [3, 5, 7, 11] (patsG.getD 34 [])) P34.sel P34.B = true := by
  decide +kernel

e4_data P35 G [3, 5, 7, 11] 35
theorem ok35 : macCheckK 3 8 pE sE (formsGK [3, 5, 7, 11] (patsG.getD 35 [])) P35.sel P35.B = true := by
  decide +kernel

e4_data P36 G [3, 5, 7, 11] 36
theorem ok36 : macCheckK 3 8 pE sE (formsGK [3, 5, 7, 11] (patsG.getD 36 [])) P36.sel P36.B = true := by
  decide +kernel

e4_data P37 G [3, 5, 7, 11] 37
theorem ok37 : macCheckK 3 8 pE sE (formsGK [3, 5, 7, 11] (patsG.getD 37 [])) P37.sel P37.B = true := by
  decide +kernel

e4_data P38 G [3, 5, 7, 11] 38
theorem ok38 : macCheckK 3 8 pE sE (formsGK [3, 5, 7, 11] (patsG.getD 38 [])) P38.sel P38.B = true := by
  decide +kernel

e4_data P39 G [3, 5, 7, 11] 39
theorem ok39 : macCheckK 3 8 pE sE (formsGK [3, 5, 7, 11] (patsG.getD 39 [])) P39.sel P39.B = true := by
  decide +kernel

end L6CheckKSpec.E4.G3_5_7_11
