import L6KSpec.E4Data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Macaulay checks of the forms `F` at `μ = (1, 1, 1, 1)`, patterns 256–263. -/

namespace L6CheckKSpec.E4.F1111

open Lean6.Special.Comp Lean6.Special.Comp.E4 L6KSpec.E4

e4_data P256 F [1, 1, 1, 1] 256
theorem ok256 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 256 [])) P256.sel P256.B = true := by
  decide +kernel

e4_data P257 F [1, 1, 1, 1] 257
theorem ok257 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 257 [])) P257.sel P257.B = true := by
  decide +kernel

e4_data P258 F [1, 1, 1, 1] 258
theorem ok258 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 258 [])) P258.sel P258.B = true := by
  decide +kernel

e4_data P259 F [1, 1, 1, 1] 259
theorem ok259 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 259 [])) P259.sel P259.B = true := by
  decide +kernel

e4_data P260 F [1, 1, 1, 1] 260
theorem ok260 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 260 [])) P260.sel P260.B = true := by
  decide +kernel

e4_data P261 F [1, 1, 1, 1] 261
theorem ok261 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 261 [])) P261.sel P261.B = true := by
  decide +kernel

e4_data P262 F [1, 1, 1, 1] 262
theorem ok262 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 262 [])) P262.sel P262.B = true := by
  decide +kernel

e4_data P263 F [1, 1, 1, 1] 263
theorem ok263 : macCheckK 4 7 pE sE (formsF [1, 1, 1, 1] (patsF.getD 263 [])) P263.sel P263.B = true := by
  decide +kernel

end L6CheckKSpec.E4.F1111
