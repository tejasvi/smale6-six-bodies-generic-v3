import L6CheckK.F1.All

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The codes in the interval 11. -/

namespace L6CheckK.F1.Codes.C11

open L6F1 L6K.F1 L6CheckK.F1

theorem ok : ivlCheck codesAll repCodes.flatten 67729744576 68262494308 = true := by decide +kernel

end L6CheckK.F1.Codes.C11
