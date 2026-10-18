import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C76

namespace L6.F2S.Checks

open L6.F2S

/-- The number of pairs of trees of class 76 after 3 insertions. -/
theorem f2s_len_c76 : (prefixPairs keepLP (L6.F2.diagOf 76) 3).length = 60 := by native_decide

set_option maxHeartbeats 0 in
/-- Every cell of the specification search of class 76 has the key of a stored line. -/
theorem f2s_c76 : checkBelow keepLP (L6.F2.diagOf 76) 3 L6.F2.Data.cells_c76 (prefixPairs keepLP (L6.F2.diagOf 76) 3) = true := by
  native_decide

end L6.F2S.Checks
