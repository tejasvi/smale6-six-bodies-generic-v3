import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C148

namespace L6.F2S.Checks

open L6.F2S

set_option maxHeartbeats 0 in
/-- Class 148, the pairs 408 ≤ i < 416 after 4 insertions. -/
theorem f2s_c148_m51 : checkBelow keepLP (L6.F2.diagOf 148) 4 L6.F2.Data.cells_c148
    (((prefixPairs keepLP (L6.F2.diagOf 148) 4).drop 408).take 8) = true := by
  native_decide

end L6.F2S.Checks
