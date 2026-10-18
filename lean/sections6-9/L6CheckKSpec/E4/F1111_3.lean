import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 24–31. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P24 F [1, 1, 1, 1] 24
theorem ok24 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 24 [])) P24.sel P24.B = true := by
  decide +kernel

e4_data P25 F [1, 1, 1, 1] 25
theorem ok25 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 25 [])) P25.sel P25.B = true := by
  decide +kernel

e4_data P26 F [1, 1, 1, 1] 26
theorem ok26 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 26 [])) P26.sel P26.B = true := by
  decide +kernel

e4_data P27 F [1, 1, 1, 1] 27
theorem ok27 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 27 [])) P27.sel P27.B = true := by
  decide +kernel

e4_data P28 F [1, 1, 1, 1] 28
theorem ok28 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 28 [])) P28.sel P28.B = true := by
  decide +kernel

e4_data P29 F [1, 1, 1, 1] 29
theorem ok29 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 29 [])) P29.sel P29.B = true := by
  decide +kernel

e4_data P30 F [1, 1, 1, 1] 30
theorem ok30 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 30 [])) P30.sel P30.B = true := by
  decide +kernel

e4_data P31 F [1, 1, 1, 1] 31
theorem ok31 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 31 [])) P31.sel P31.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
