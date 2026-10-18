import L6CheckKSpec.KC.M27
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M27`. -/

namespace L6CheckKSpec.KC.Cnt27

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M27.boxes = some (0, 64, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt27
