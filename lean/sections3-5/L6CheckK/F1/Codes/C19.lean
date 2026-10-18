import L6CheckK.F1.All

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The codes in the interval 19. -/

namespace L6CheckK.F1.Codes.C19

open L6F1 L6K.F1 L6CheckK.F1

theorem ok : ivlCheck codesAll repCodes.flatten 1924161210507 2287239972864 = true := by decide +kernel

end L6CheckK.F1.Codes.C19
