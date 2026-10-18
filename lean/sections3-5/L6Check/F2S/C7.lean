import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C7

namespace L6.F2S.Checks

open L6.F2S

/-- The number of pairs of trees of class 7 after 3 insertions. -/
theorem f2s_len_c7 : (prefixPairs keepLP (L6.F2.diagOf 7) 3).length = 40 := by native_decide

set_option maxHeartbeats 0 in
/-- Every cell of the specification search of class 7 has the key of a stored line. -/
theorem f2s_c7 : checkBelow keepLP (L6.F2.diagOf 7) 3 L6.F2.Data.cells_c7 (prefixPairs keepLP (L6.F2.diagOf 7) 3) = true := by
  native_decide

end L6.F2S.Checks
