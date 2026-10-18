import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 560–567. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P560 F [1, 1, 1, 1] 560
theorem ok560 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 560 [])) P560.sel P560.B = true := by
  decide +kernel

e4_data P561 F [1, 1, 1, 1] 561
theorem ok561 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 561 [])) P561.sel P561.B = true := by
  decide +kernel

e4_data P562 F [1, 1, 1, 1] 562
theorem ok562 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 562 [])) P562.sel P562.B = true := by
  decide +kernel

e4_data P563 F [1, 1, 1, 1] 563
theorem ok563 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 563 [])) P563.sel P563.B = true := by
  decide +kernel

e4_data P564 F [1, 1, 1, 1] 564
theorem ok564 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 564 [])) P564.sel P564.B = true := by
  decide +kernel

e4_data P565 F [1, 1, 1, 1] 565
theorem ok565 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 565 [])) P565.sel P565.B = true := by
  decide +kernel

e4_data P566 F [1, 1, 1, 1] 566
theorem ok566 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 566 [])) P566.sel P566.B = true := by
  decide +kernel

e4_data P567 F [1, 1, 1, 1] 567
theorem ok567 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 567 [])) P567.sel P567.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
