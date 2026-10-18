import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 288–295. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P288 F [1, 1, 1, 1] 288
theorem ok288 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 288 [])) P288.sel P288.B = true := by
  decide +kernel

e4_data P289 F [1, 1, 1, 1] 289
theorem ok289 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 289 [])) P289.sel P289.B = true := by
  decide +kernel

e4_data P290 F [1, 1, 1, 1] 290
theorem ok290 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 290 [])) P290.sel P290.B = true := by
  decide +kernel

e4_data P291 F [1, 1, 1, 1] 291
theorem ok291 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 291 [])) P291.sel P291.B = true := by
  decide +kernel

e4_data P292 F [1, 1, 1, 1] 292
theorem ok292 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 292 [])) P292.sel P292.B = true := by
  decide +kernel

e4_data P293 F [1, 1, 1, 1] 293
theorem ok293 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 293 [])) P293.sel P293.B = true := by
  decide +kernel

e4_data P294 F [1, 1, 1, 1] 294
theorem ok294 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 294 [])) P294.sel P294.B = true := by
  decide +kernel

e4_data P295 F [1, 1, 1, 1] 295
theorem ok295 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 295 [])) P295.sel P295.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
