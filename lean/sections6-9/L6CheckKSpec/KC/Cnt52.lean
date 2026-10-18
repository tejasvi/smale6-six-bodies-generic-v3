import L6CheckKSpec.KC.M52
import L6KSpec.Counts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The classes of the boxes of `KC.M52`. -/

namespace L6CheckKSpec.KC.Cnt52

theorem cnt : L6KSpec.kcCountsB L6CheckKSpec.KC.M52.boxes = some (40, 24, 0) := by decide +kernel

end L6CheckKSpec.KC.Cnt52
