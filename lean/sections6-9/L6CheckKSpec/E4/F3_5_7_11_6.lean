import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 48–55. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P48 F [3, 5, 7, 11] 48
theorem ok48 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 48 [])) P48.sel P48.B = true := by
  decide +kernel

e4_data P49 F [3, 5, 7, 11] 49
theorem ok49 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 49 [])) P49.sel P49.B = true := by
  decide +kernel

e4_data P50 F [3, 5, 7, 11] 50
theorem ok50 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 50 [])) P50.sel P50.B = true := by
  decide +kernel

e4_data P51 F [3, 5, 7, 11] 51
theorem ok51 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 51 [])) P51.sel P51.B = true := by
  decide +kernel

e4_data P52 F [3, 5, 7, 11] 52
theorem ok52 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 52 [])) P52.sel P52.B = true := by
  decide +kernel

e4_data P53 F [3, 5, 7, 11] 53
theorem ok53 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 53 [])) P53.sel P53.B = true := by
  decide +kernel

e4_data P54 F [3, 5, 7, 11] 54
theorem ok54 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 54 [])) P54.sel P54.B = true := by
  decide +kernel

e4_data P55 F [3, 5, 7, 11] 55
theorem ok55 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 55 [])) P55.sel P55.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
