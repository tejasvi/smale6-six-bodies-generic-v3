import L6CheckKSpec.KC.M71
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M71`. -/

namespace L6CheckKSpec.KC.Cnt71

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M71.boxes = some (36, 28, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt71
