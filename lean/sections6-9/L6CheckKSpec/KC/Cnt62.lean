import L6CheckKSpec.KC.M62
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M62`. -/

namespace L6CheckKSpec.KC.Cnt62

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M62.boxes = some (52, 12, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt62
