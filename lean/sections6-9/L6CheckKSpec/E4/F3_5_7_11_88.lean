import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 704–711. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P704 F [3, 5, 7, 11] 704
theorem ok704 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 704 [])) P704.sel P704.B = true := by
  decide +kernel

e4_data P705 F [3, 5, 7, 11] 705
theorem ok705 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 705 [])) P705.sel P705.B = true := by
  decide +kernel

e4_data P706 F [3, 5, 7, 11] 706
theorem ok706 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 706 [])) P706.sel P706.B = true := by
  decide +kernel

e4_data P707 F [3, 5, 7, 11] 707
theorem ok707 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 707 [])) P707.sel P707.B = true := by
  decide +kernel

e4_data P708 F [3, 5, 7, 11] 708
theorem ok708 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 708 [])) P708.sel P708.B = true := by
  decide +kernel

e4_data P709 F [3, 5, 7, 11] 709
theorem ok709 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 709 [])) P709.sel P709.B = true := by
  decide +kernel

e4_data P710 F [3, 5, 7, 11] 710
theorem ok710 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 710 [])) P710.sel P710.B = true := by
  decide +kernel

e4_data P711 F [3, 5, 7, 11] 711
theorem ok711 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 711 [])) P711.sel P711.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
