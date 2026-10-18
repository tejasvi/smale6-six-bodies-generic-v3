import L6CheckKSpec.KC.M54
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M54`. -/

namespace L6CheckKSpec.KC.Cnt54

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M54.boxes = some (12, 52, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt54
