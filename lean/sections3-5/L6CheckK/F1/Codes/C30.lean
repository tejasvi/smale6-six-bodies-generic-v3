import L6CheckK.F1.All

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The codes in the interval 30. -/

namespace L6CheckK.F1.Codes.C30

open L6F1 L6K.F1 L6CheckK.F1

theorem ok : ivlCheck codesAll repCodes.flatten 4397111771240 4397425787139 = true := by decide +kernel

end L6CheckK.F1.Codes.C30
