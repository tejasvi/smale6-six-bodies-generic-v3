import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 576–583. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P576 F [1, 1, 1, 1] 576
theorem ok576 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 576 [])) P576.sel P576.B = true := by
  decide +kernel

e4_data P577 F [1, 1, 1, 1] 577
theorem ok577 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 577 [])) P577.sel P577.B = true := by
  decide +kernel

e4_data P578 F [1, 1, 1, 1] 578
theorem ok578 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 578 [])) P578.sel P578.B = true := by
  decide +kernel

e4_data P579 F [1, 1, 1, 1] 579
theorem ok579 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 579 [])) P579.sel P579.B = true := by
  decide +kernel

e4_data P580 F [1, 1, 1, 1] 580
theorem ok580 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 580 [])) P580.sel P580.B = true := by
  decide +kernel

e4_data P581 F [1, 1, 1, 1] 581
theorem ok581 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 581 [])) P581.sel P581.B = true := by
  decide +kernel

e4_data P582 F [1, 1, 1, 1] 582
theorem ok582 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 582 [])) P582.sel P582.B = true := by
  decide +kernel

e4_data P583 F [1, 1, 1, 1] 583
theorem ok583 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 583 [])) P583.sel P583.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
