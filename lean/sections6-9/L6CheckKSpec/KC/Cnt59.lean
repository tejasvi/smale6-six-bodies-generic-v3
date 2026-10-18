import L6CheckKSpec.KC.M59
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M59`. -/

namespace L6CheckKSpec.KC.Cnt59

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M59.boxes = some (42, 22, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt59
