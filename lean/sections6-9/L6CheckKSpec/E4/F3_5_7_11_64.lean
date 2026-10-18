import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 512–519. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P512 F [3, 5, 7, 11] 512
theorem ok512 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 512 [])) P512.sel P512.B = true := by
  decide +kernel

e4_data P513 F [3, 5, 7, 11] 513
theorem ok513 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 513 [])) P513.sel P513.B = true := by
  decide +kernel

e4_data P514 F [3, 5, 7, 11] 514
theorem ok514 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 514 [])) P514.sel P514.B = true := by
  decide +kernel

e4_data P515 F [3, 5, 7, 11] 515
theorem ok515 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 515 [])) P515.sel P515.B = true := by
  decide +kernel

e4_data P516 F [3, 5, 7, 11] 516
theorem ok516 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 516 [])) P516.sel P516.B = true := by
  decide +kernel

e4_data P517 F [3, 5, 7, 11] 517
theorem ok517 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 517 [])) P517.sel P517.B = true := by
  decide +kernel

e4_data P518 F [3, 5, 7, 11] 518
theorem ok518 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 518 [])) P518.sel P518.B = true := by
  decide +kernel

e4_data P519 F [3, 5, 7, 11] 519
theorem ok519 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 519 [])) P519.sel P519.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
