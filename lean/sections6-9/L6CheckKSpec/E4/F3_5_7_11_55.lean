import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 440–447. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P440 F [3, 5, 7, 11] 440
theorem ok440 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 440 [])) P440.sel P440.B = true := by
  decide +kernel

e4_data P441 F [3, 5, 7, 11] 441
theorem ok441 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 441 [])) P441.sel P441.B = true := by
  decide +kernel

e4_data P442 F [3, 5, 7, 11] 442
theorem ok442 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 442 [])) P442.sel P442.B = true := by
  decide +kernel

e4_data P443 F [3, 5, 7, 11] 443
theorem ok443 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 443 [])) P443.sel P443.B = true := by
  decide +kernel

e4_data P444 F [3, 5, 7, 11] 444
theorem ok444 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 444 [])) P444.sel P444.B = true := by
  decide +kernel

e4_data P445 F [3, 5, 7, 11] 445
theorem ok445 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 445 [])) P445.sel P445.B = true := by
  decide +kernel

e4_data P446 F [3, 5, 7, 11] 446
theorem ok446 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 446 [])) P446.sel P446.B = true := by
  decide +kernel

e4_data P447 F [3, 5, 7, 11] 447
theorem ok447 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 447 [])) P447.sel P447.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
