import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `G` at `μ = (1, 1, 1, 1)`, patterns 24–31. -/

namespace L6CheckKSpec.E4.G1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P24 G [1, 1, 1, 1] 24
theorem ok24 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 24 [])) P24.sel P24.B = true := by
  decide +kernel

e4_data P25 G [1, 1, 1, 1] 25
theorem ok25 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 25 [])) P25.sel P25.B = true := by
  decide +kernel

e4_data P26 G [1, 1, 1, 1] 26
theorem ok26 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 26 [])) P26.sel P26.B = true := by
  decide +kernel

e4_data P27 G [1, 1, 1, 1] 27
theorem ok27 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 27 [])) P27.sel P27.B = true := by
  decide +kernel

e4_data P28 G [1, 1, 1, 1] 28
theorem ok28 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 28 [])) P28.sel P28.B = true := by
  decide +kernel

e4_data P29 G [1, 1, 1, 1] 29
theorem ok29 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 29 [])) P29.sel P29.B = true := by
  decide +kernel

e4_data P30 G [1, 1, 1, 1] 30
theorem ok30 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 30 [])) P30.sel P30.B = true := by
  decide +kernel

e4_data P31 G [1, 1, 1, 1] 31
theorem ok31 : macCheckK 3 8 pE sE (formsGK [1, 1, 1, 1] (patsG.getD 31 [])) P31.sel P31.B = true := by
  decide +kernel

end L6CheckKSpec.E4.G1111
