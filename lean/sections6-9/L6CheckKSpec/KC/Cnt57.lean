import L6CheckKSpec.KC.M57
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M57`. -/

namespace L6CheckKSpec.KC.Cnt57

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M57.boxes = some (30, 34, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt57
