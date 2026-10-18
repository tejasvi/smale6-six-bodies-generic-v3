import L6CheckKSpec.KC.M45
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M45`. -/

namespace L6CheckKSpec.KC.Cnt45

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M45.boxes = some (10, 54, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt45
