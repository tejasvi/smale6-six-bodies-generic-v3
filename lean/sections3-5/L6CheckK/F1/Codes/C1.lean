import L6CheckK.F1.All

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The codes in the interval 1. -/

namespace L6CheckK.F1.Codes.C1

open L6F1 L6K.F1 L6CheckK.F1

theorem ok : ivlCheck codesAll repCodes.flatten 272637808 3495577601 = true := by decide +kernel

end L6CheckK.F1.Codes.C1
