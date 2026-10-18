import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 584–591. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P584 F [1, 1, 1, 1] 584
theorem ok584 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 584 [])) P584.sel P584.B = true := by
  decide +kernel

e4_data P585 F [1, 1, 1, 1] 585
theorem ok585 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 585 [])) P585.sel P585.B = true := by
  decide +kernel

e4_data P586 F [1, 1, 1, 1] 586
theorem ok586 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 586 [])) P586.sel P586.B = true := by
  decide +kernel

e4_data P587 F [1, 1, 1, 1] 587
theorem ok587 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 587 [])) P587.sel P587.B = true := by
  decide +kernel

e4_data P588 F [1, 1, 1, 1] 588
theorem ok588 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 588 [])) P588.sel P588.B = true := by
  decide +kernel

e4_data P589 F [1, 1, 1, 1] 589
theorem ok589 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 589 [])) P589.sel P589.B = true := by
  decide +kernel

e4_data P590 F [1, 1, 1, 1] 590
theorem ok590 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 590 [])) P590.sel P590.B = true := by
  decide +kernel

e4_data P591 F [1, 1, 1, 1] 591
theorem ok591 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 591 [])) P591.sel P591.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
