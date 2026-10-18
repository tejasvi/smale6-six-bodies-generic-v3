import L6CheckKSpec.KC.M70
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M70`. -/

namespace L6CheckKSpec.KC.Cnt70

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M70.boxes = some (20, 44, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt70
