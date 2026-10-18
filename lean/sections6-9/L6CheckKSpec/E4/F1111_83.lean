import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 664–671. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P664 F [1, 1, 1, 1] 664
theorem ok664 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 664 [])) P664.sel P664.B = true := by
  decide +kernel

e4_data P665 F [1, 1, 1, 1] 665
theorem ok665 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 665 [])) P665.sel P665.B = true := by
  decide +kernel

e4_data P666 F [1, 1, 1, 1] 666
theorem ok666 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 666 [])) P666.sel P666.B = true := by
  decide +kernel

e4_data P667 F [1, 1, 1, 1] 667
theorem ok667 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 667 [])) P667.sel P667.B = true := by
  decide +kernel

e4_data P668 F [1, 1, 1, 1] 668
theorem ok668 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 668 [])) P668.sel P668.B = true := by
  decide +kernel

e4_data P669 F [1, 1, 1, 1] 669
theorem ok669 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 669 [])) P669.sel P669.B = true := by
  decide +kernel

e4_data P670 F [1, 1, 1, 1] 670
theorem ok670 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 670 [])) P670.sel P670.B = true := by
  decide +kernel

e4_data P671 F [1, 1, 1, 1] 671
theorem ok671 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 671 [])) P671.sel P671.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
