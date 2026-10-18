import L6CheckK.F1.All

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The codes in the interval 9. -/

namespace L6CheckK.F1.Codes.C9

open L6F1 L6K.F1 L6CheckK.F1

theorem ok : ivlCheck codesAll repCodes.flatten 60465090623 67427829073 = true := by decide +kernel

end L6CheckK.F1.Codes.C9
