import L6CheckKSpec.KC.M46
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M46`. -/

namespace L6CheckKSpec.KC.Cnt46

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M46.boxes = some (58, 6, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt46
