import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C168

namespace L6.F2S.Checks

open L6.F2S

/-- The number of pairs of trees of class 168 after 3 insertions. -/
theorem f2s_len_c168 : (prefixPairs keepLP (L6.F2.diagOf 168) 3).length = 0 := by native_decide

set_option maxHeartbeats 0 in
/-- Every cell of the specification search of class 168 has the key of a stored line. -/
theorem f2s_c168 : checkBelow keepLP (L6.F2.diagOf 168) 3 L6.F2.Data.cells_c168 (prefixPairs keepLP (L6.F2.diagOf 168) 3) = true := by
  native_decide

end L6.F2S.Checks
