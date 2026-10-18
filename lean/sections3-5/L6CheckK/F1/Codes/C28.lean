import L6CheckK.F1.All

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The codes in the interval 28. -/

namespace L6CheckK.F1.Codes.C28

open L6F1 L6K.F1 L6CheckK.F1

theorem ok : ivlCheck codesAll repCodes.flatten 4330182869642 4396997988808 = true := by decide +kernel

end L6CheckK.F1.Codes.C28
