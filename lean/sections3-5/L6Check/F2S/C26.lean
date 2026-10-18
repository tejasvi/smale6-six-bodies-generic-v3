import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C26

namespace L6.F2S.Checks

open L6.F2S

/-- The number of pairs of trees of class 26 after 3 insertions. -/
theorem f2s_len_c26 : (prefixPairs keepLP (L6.F2.diagOf 26) 3).length = 0 := by native_decide

set_option maxHeartbeats 0 in
/-- Every cell of the specification search of class 26 has the key of a stored line. -/
theorem f2s_c26 : checkBelow keepLP (L6.F2.diagOf 26) 3 L6.F2.Data.cells_c26 (prefixPairs keepLP (L6.F2.diagOf 26) 3) = true := by
  native_decide

end L6.F2S.Checks
