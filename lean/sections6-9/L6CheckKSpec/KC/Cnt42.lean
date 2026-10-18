import L6CheckKSpec.KC.M42
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M42`. -/

namespace L6CheckKSpec.KC.Cnt42

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M42.boxes = some (0, 64, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt42
