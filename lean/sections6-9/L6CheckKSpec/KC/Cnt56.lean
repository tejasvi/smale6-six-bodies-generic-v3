import L6CheckKSpec.KC.M56
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M56`. -/

namespace L6CheckKSpec.KC.Cnt56

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M56.boxes = some (42, 22, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt56
