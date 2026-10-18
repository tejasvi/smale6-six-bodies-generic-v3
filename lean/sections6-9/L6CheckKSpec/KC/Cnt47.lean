import L6CheckKSpec.KC.M47
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M47`. -/

namespace L6CheckKSpec.KC.Cnt47

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M47.boxes = some (16, 48, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt47
