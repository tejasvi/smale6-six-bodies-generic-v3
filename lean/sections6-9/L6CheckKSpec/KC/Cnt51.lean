import L6CheckKSpec.KC.M51
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M51`. -/

namespace L6CheckKSpec.KC.Cnt51

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M51.boxes = some (22, 42, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt51
