import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 504–511. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P504 F [1, 1, 1, 1] 504
theorem ok504 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 504 [])) P504.sel P504.B = true := by
  decide +kernel

e4_data P505 F [1, 1, 1, 1] 505
theorem ok505 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 505 [])) P505.sel P505.B = true := by
  decide +kernel

e4_data P506 F [1, 1, 1, 1] 506
theorem ok506 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 506 [])) P506.sel P506.B = true := by
  decide +kernel

e4_data P507 F [1, 1, 1, 1] 507
theorem ok507 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 507 [])) P507.sel P507.B = true := by
  decide +kernel

e4_data P508 F [1, 1, 1, 1] 508
theorem ok508 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 508 [])) P508.sel P508.B = true := by
  decide +kernel

e4_data P509 F [1, 1, 1, 1] 509
theorem ok509 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 509 [])) P509.sel P509.B = true := by
  decide +kernel

e4_data P510 F [1, 1, 1, 1] 510
theorem ok510 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 510 [])) P510.sel P510.B = true := by
  decide +kernel

e4_data P511 F [1, 1, 1, 1] 511
theorem ok511 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 511 [])) P511.sel P511.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
