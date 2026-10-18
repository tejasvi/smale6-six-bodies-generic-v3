import L6CheckKSpec.KC.M60
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M60`. -/

namespace L6CheckKSpec.KC.Cnt60

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M60.boxes = some (58, 6, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt60
