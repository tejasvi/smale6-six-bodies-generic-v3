import L6CheckKSpec.KC.M72
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M72`. -/

namespace L6CheckKSpec.KC.Cnt72

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M72.boxes = some (64, 0, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt72
