import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `G` at `μ = (1, 1, 1, 1)`, patterns 8–15. -/

namespace L6CheckKSpec.E4.G1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P8 G [1, 1, 1, 1] 8
theorem ok8 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 8 [])) P8.sel P8.B = true := by
  decide +kernel

e4_data P9 G [1, 1, 1, 1] 9
theorem ok9 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 9 [])) P9.sel P9.B = true := by
  decide +kernel

e4_data P10 G [1, 1, 1, 1] 10
theorem ok10 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 10 [])) P10.sel P10.B = true := by
  decide +kernel

e4_data P11 G [1, 1, 1, 1] 11
theorem ok11 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 11 [])) P11.sel P11.B = true := by
  decide +kernel

e4_data P12 G [1, 1, 1, 1] 12
theorem ok12 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 12 [])) P12.sel P12.B = true := by
  decide +kernel

e4_data P13 G [1, 1, 1, 1] 13
theorem ok13 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 13 [])) P13.sel P13.B = true := by
  decide +kernel

e4_data P14 G [1, 1, 1, 1] 14
theorem ok14 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 14 [])) P14.sel P14.B = true := by
  decide +kernel

e4_data P15 G [1, 1, 1, 1] 15
theorem ok15 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 15 [])) P15.sel P15.B = true := by
  decide +kernel

end L6CheckKSpec.E4.G1111
