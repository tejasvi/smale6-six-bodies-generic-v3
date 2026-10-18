import L6CheckKSpec.KC.M32
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M32`. -/

namespace L6CheckKSpec.KC.Cnt32

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M32.boxes = some (0, 64, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt32
