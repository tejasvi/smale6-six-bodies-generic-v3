import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (3, 5, 7, 11)`, patterns 656–663. -/

namespace L6CheckKSpec.E4.F3_5_7_11

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P656 F [3, 5, 7, 11] 656
theorem ok656 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 656 [])) P656.sel P656.B = true := by
  decide +kernel

e4_data P657 F [3, 5, 7, 11] 657
theorem ok657 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 657 [])) P657.sel P657.B = true := by
  decide +kernel

e4_data P658 F [3, 5, 7, 11] 658
theorem ok658 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 658 [])) P658.sel P658.B = true := by
  decide +kernel

e4_data P659 F [3, 5, 7, 11] 659
theorem ok659 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 659 [])) P659.sel P659.B = true := by
  decide +kernel

e4_data P660 F [3, 5, 7, 11] 660
theorem ok660 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 660 [])) P660.sel P660.B = true := by
  decide +kernel

e4_data P661 F [3, 5, 7, 11] 661
theorem ok661 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 661 [])) P661.sel P661.B = true := by
  decide +kernel

e4_data P662 F [3, 5, 7, 11] 662
theorem ok662 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 662 [])) P662.sel P662.B = true := by
  decide +kernel

e4_data P663 F [3, 5, 7, 11] 663
theorem ok663 : macCheckK 4 7 pE sE (formsF [3, 5, 7, 11] (patsF.getD 663 [])) P663.sel P663.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F3_5_7_11
