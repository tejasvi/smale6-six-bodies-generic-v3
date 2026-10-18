import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 352–359. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P352 F [1, 1, 1, 1] 352
theorem ok352 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 352 [])) P352.sel P352.B = true := by
  decide +kernel

e4_data P353 F [1, 1, 1, 1] 353
theorem ok353 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 353 [])) P353.sel P353.B = true := by
  decide +kernel

e4_data P354 F [1, 1, 1, 1] 354
theorem ok354 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 354 [])) P354.sel P354.B = true := by
  decide +kernel

e4_data P355 F [1, 1, 1, 1] 355
theorem ok355 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 355 [])) P355.sel P355.B = true := by
  decide +kernel

e4_data P356 F [1, 1, 1, 1] 356
theorem ok356 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 356 [])) P356.sel P356.B = true := by
  decide +kernel

e4_data P357 F [1, 1, 1, 1] 357
theorem ok357 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 357 [])) P357.sel P357.B = true := by
  decide +kernel

e4_data P358 F [1, 1, 1, 1] 358
theorem ok358 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 358 [])) P358.sel P358.B = true := by
  decide +kernel

e4_data P359 F [1, 1, 1, 1] 359
theorem ok359 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 359 [])) P359.sel P359.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
