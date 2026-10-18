import L6CheckKSpec.KC.M26
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M26`. -/

namespace L6CheckKSpec.KC.Cnt26

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M26.boxes = some (12, 52, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt26
