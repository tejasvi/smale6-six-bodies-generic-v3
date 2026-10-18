import L6CheckKSpec.KC.M13
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M13`. -/

namespace L6CheckKSpec.KC.Cnt13

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M13.boxes = some (0, 64, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt13
