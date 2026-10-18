import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C128

namespace L6.F2S.Checks

open L6.F2S

set_option maxHeartbeats 0 in
/-- Class 128, the pairs 120 ≤ i < 128 after 4 insertions. -/
theorem f2s_c128_m15 : checkBelow keepLP (L6.F2.diagOf 128) 4 L6.F2.Data.cells_c128
    (((prefixPairs keepLP (L6.F2.diagOf 128) 4).drop 120).take 8) = true := by
  native_decide

end L6.F2S.Checks
