import L6CheckKSpec.KC.M1
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M1`. -/

namespace L6CheckKSpec.KC.Cnt1

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M1.boxes = some (8, 56, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt1
