import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C141

namespace L6.F2S.Checks

open L6.F2S

/-- The number of pairs of trees of class 141 after 3 insertions. -/
theorem f2s_len_c141 : (prefixPairs keepLP (L6.F2.diagOf 141) 3).length = 16 := by native_decide

set_option maxHeartbeats 0 in
/-- Every cell of the specification search of class 141 has the key of a stored line. -/
theorem f2s_c141 : checkBelow keepLP (L6.F2.diagOf 141) 3 L6.F2.Data.cells_c141 (prefixPairs keepLP (L6.F2.diagOf 141) 3) = true := by
  native_decide

end L6.F2S.Checks
