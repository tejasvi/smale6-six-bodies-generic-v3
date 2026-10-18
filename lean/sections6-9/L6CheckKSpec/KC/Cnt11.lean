import L6CheckKSpec.KC.M11
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M11`. -/

namespace L6CheckKSpec.KC.Cnt11

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M11.boxes = some (0, 64, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt11
