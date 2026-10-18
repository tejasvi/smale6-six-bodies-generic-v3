import L6CheckKSpec.KC.M19
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M19`. -/

namespace L6CheckKSpec.KC.Cnt19

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M19.boxes = some (0, 64, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt19
