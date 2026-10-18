import L6CheckKSpec.KC.M68
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M68`. -/

namespace L6CheckKSpec.KC.Cnt68

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M68.boxes = some (64, 0, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt68
