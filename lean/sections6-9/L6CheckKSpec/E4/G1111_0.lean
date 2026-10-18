import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `G` at `μ = (1, 1, 1, 1)`, patterns 0–7. -/

namespace L6CheckKSpec.E4.G1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P0 G [1, 1, 1, 1] 0
theorem ok0 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 0 [])) P0.sel P0.B = true := by
  decide +kernel

e4_data P1 G [1, 1, 1, 1] 1
theorem ok1 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 1 [])) P1.sel P1.B = true := by
  decide +kernel

e4_data P2 G [1, 1, 1, 1] 2
theorem ok2 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 2 [])) P2.sel P2.B = true := by
  decide +kernel

e4_data P3 G [1, 1, 1, 1] 3
theorem ok3 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 3 [])) P3.sel P3.B = true := by
  decide +kernel

e4_data P4 G [1, 1, 1, 1] 4
theorem ok4 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 4 [])) P4.sel P4.B = true := by
  decide +kernel

e4_data P5 G [1, 1, 1, 1] 5
theorem ok5 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 5 [])) P5.sel P5.B = true := by
  decide +kernel

e4_data P6 G [1, 1, 1, 1] 6
theorem ok6 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 6 [])) P6.sel P6.B = true := by
  decide +kernel

e4_data P7 G [1, 1, 1, 1] 7
theorem ok7 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 7 [])) P7.sel P7.B = true := by
  decide +kernel

end L6CheckKSpec.E4.G1111
