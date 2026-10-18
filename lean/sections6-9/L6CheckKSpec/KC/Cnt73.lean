import L6CheckKSpec.KC.M73
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M73`. -/

namespace L6CheckKSpec.KC.Cnt73

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M73.boxes = some (64, 0, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt73
