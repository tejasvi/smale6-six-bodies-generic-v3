import L6CheckKSpec.KC.M67
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M67`. -/

namespace L6CheckKSpec.KC.Cnt67

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M67.boxes = some (32, 32, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt67
