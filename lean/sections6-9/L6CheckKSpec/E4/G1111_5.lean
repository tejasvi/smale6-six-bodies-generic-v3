import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `G` at `μ = (1, 1, 1, 1)`, patterns 40–47. -/

namespace L6CheckKSpec.E4.G1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P40 G [1, 1, 1, 1] 40
theorem ok40 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 40 [])) P40.sel P40.B = true := by
  decide +kernel

e4_data P41 G [1, 1, 1, 1] 41
theorem ok41 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 41 [])) P41.sel P41.B = true := by
  decide +kernel

e4_data P42 G [1, 1, 1, 1] 42
theorem ok42 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 42 [])) P42.sel P42.B = true := by
  decide +kernel

e4_data P43 G [1, 1, 1, 1] 43
theorem ok43 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 43 [])) P43.sel P43.B = true := by
  decide +kernel

e4_data P44 G [1, 1, 1, 1] 44
theorem ok44 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 44 [])) P44.sel P44.B = true := by
  decide +kernel

e4_data P45 G [1, 1, 1, 1] 45
theorem ok45 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 45 [])) P45.sel P45.B = true := by
  decide +kernel

e4_data P46 G [1, 1, 1, 1] 46
theorem ok46 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 46 [])) P46.sel P46.B = true := by
  decide +kernel

e4_data P47 G [1, 1, 1, 1] 47
theorem ok47 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 47 [])) P47.sel P47.B = true := by
  decide +kernel

end L6CheckKSpec.E4.G1111
