import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C3

namespace L6.F2S.Checks

open L6.F2S

set_option maxHeartbeats 0 in
/-- Class 3, the pairs 424 ≤ i < 432 after 4 insertions. -/
theorem f2s_c3_m53 : checkBelow keepLP (L6.F2.diagOf 3) 4 L6.F2.Data.cells_c3
    (((prefixPairs keepLP (L6.F2.diagOf 3) 4).drop 424).take 8) = true := by
  native_decide

end L6.F2S.Checks
