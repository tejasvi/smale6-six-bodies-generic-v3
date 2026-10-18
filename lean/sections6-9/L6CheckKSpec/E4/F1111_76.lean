import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 608–615. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P608 F [1, 1, 1, 1] 608
theorem ok608 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 608 [])) P608.sel P608.B = true := by
  decide +kernel

e4_data P609 F [1, 1, 1, 1] 609
theorem ok609 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 609 [])) P609.sel P609.B = true := by
  decide +kernel

e4_data P610 F [1, 1, 1, 1] 610
theorem ok610 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 610 [])) P610.sel P610.B = true := by
  decide +kernel

e4_data P611 F [1, 1, 1, 1] 611
theorem ok611 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 611 [])) P611.sel P611.B = true := by
  decide +kernel

e4_data P612 F [1, 1, 1, 1] 612
theorem ok612 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 612 [])) P612.sel P612.B = true := by
  decide +kernel

e4_data P613 F [1, 1, 1, 1] 613
theorem ok613 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 613 [])) P613.sel P613.B = true := by
  decide +kernel

e4_data P614 F [1, 1, 1, 1] 614
theorem ok614 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 614 [])) P614.sel P614.B = true := by
  decide +kernel

e4_data P615 F [1, 1, 1, 1] 615
theorem ok615 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 615 [])) P615.sel P615.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
