import L6CheckKSpec.KC.M53
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M53`. -/

namespace L6CheckKSpec.KC.Cnt53

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M53.boxes = some (28, 36, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt53
