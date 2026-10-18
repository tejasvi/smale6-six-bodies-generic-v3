import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `G` at `μ = (1, 1, 1, 1)`, patterns 48–55. -/

namespace L6CheckKSpec.E4.G1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P48 G [1, 1, 1, 1] 48
theorem ok48 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 48 [])) P48.sel P48.B = true := by
  decide +kernel

e4_data P49 G [1, 1, 1, 1] 49
theorem ok49 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 49 [])) P49.sel P49.B = true := by
  decide +kernel

e4_data P50 G [1, 1, 1, 1] 50
theorem ok50 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 50 [])) P50.sel P50.B = true := by
  decide +kernel

e4_data P51 G [1, 1, 1, 1] 51
theorem ok51 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 51 [])) P51.sel P51.B = true := by
  decide +kernel

e4_data P52 G [1, 1, 1, 1] 52
theorem ok52 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 52 [])) P52.sel P52.B = true := by
  decide +kernel

e4_data P53 G [1, 1, 1, 1] 53
theorem ok53 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 53 [])) P53.sel P53.B = true := by
  decide +kernel

e4_data P54 G [1, 1, 1, 1] 54
theorem ok54 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 54 [])) P54.sel P54.B = true := by
  decide +kernel

e4_data P55 G [1, 1, 1, 1] 55
theorem ok55 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 55 [])) P55.sel P55.B = true := by
  decide +kernel

end L6CheckKSpec.E4.G1111
