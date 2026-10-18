import L6CheckKSpec.KC.M0
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M0`. -/

namespace L6CheckKSpec.KC.Cnt0

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M0.boxes = some (64, 0, 36) := by decide +kernel

end L6CheckKSpec.KC.Cnt0
