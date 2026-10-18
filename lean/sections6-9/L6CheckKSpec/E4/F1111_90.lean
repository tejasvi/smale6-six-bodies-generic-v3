import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 720–727. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P720 F [1, 1, 1, 1] 720
theorem ok720 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 720 [])) P720.sel P720.B = true := by
  decide +kernel

e4_data P721 F [1, 1, 1, 1] 721
theorem ok721 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 721 [])) P721.sel P721.B = true := by
  decide +kernel

e4_data P722 F [1, 1, 1, 1] 722
theorem ok722 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 722 [])) P722.sel P722.B = true := by
  decide +kernel

e4_data P723 F [1, 1, 1, 1] 723
theorem ok723 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 723 [])) P723.sel P723.B = true := by
  decide +kernel

e4_data P724 F [1, 1, 1, 1] 724
theorem ok724 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 724 [])) P724.sel P724.B = true := by
  decide +kernel

e4_data P725 F [1, 1, 1, 1] 725
theorem ok725 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 725 [])) P725.sel P725.B = true := by
  decide +kernel

e4_data P726 F [1, 1, 1, 1] 726
theorem ok726 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 726 [])) P726.sel P726.B = true := by
  decide +kernel

e4_data P727 F [1, 1, 1, 1] 727
theorem ok727 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 727 [])) P727.sel P727.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
