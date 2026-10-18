import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 408–415. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P408 F [1, 1, 1, 1] 408
theorem ok408 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 408 [])) P408.sel P408.B = true := by
  decide +kernel

e4_data P409 F [1, 1, 1, 1] 409
theorem ok409 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 409 [])) P409.sel P409.B = true := by
  decide +kernel

e4_data P410 F [1, 1, 1, 1] 410
theorem ok410 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 410 [])) P410.sel P410.B = true := by
  decide +kernel

e4_data P411 F [1, 1, 1, 1] 411
theorem ok411 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 411 [])) P411.sel P411.B = true := by
  decide +kernel

e4_data P412 F [1, 1, 1, 1] 412
theorem ok412 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 412 [])) P412.sel P412.B = true := by
  decide +kernel

e4_data P413 F [1, 1, 1, 1] 413
theorem ok413 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 413 [])) P413.sel P413.B = true := by
  decide +kernel

e4_data P414 F [1, 1, 1, 1] 414
theorem ok414 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 414 [])) P414.sel P414.B = true := by
  decide +kernel

e4_data P415 F [1, 1, 1, 1] 415
theorem ok415 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 415 [])) P415.sel P415.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
