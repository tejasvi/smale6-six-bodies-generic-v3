import L6F2S.Stored
import L6F2.Check
import L6Check.F2.Data.C53

namespace L6.F2S.Checks

open L6.F2S

/-- The number of pairs of trees of class 53 after 3 insertions. -/
theorem f2s_len_c53 : (prefixPairs keepLP (L6.F2.diagOf 53) 3).length = 8 := by native_decide

set_option maxHeartbeats 0 in
/-- Every cell of the specification search of class 53 has the key of a stored line. -/
theorem f2s_c53 : checkBelow keepLP (L6.F2.diagOf 53) 3 L6.F2.Data.cells_c53 (prefixPairs keepLP (L6.F2.diagOf 53) 3) = true := by
  native_decide

end L6.F2S.Checks
