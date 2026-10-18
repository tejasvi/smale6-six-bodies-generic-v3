import Lean6.Special.Comp.D88.Boxes.KC.All

/-! The decisions of Sec. 6.7, last paragraph, on all boxes of Lemma 6.19(d): the T-test over the bodies 1, 2, 3 fails
on 1092 boxes and passes on 3696; the relative margin is below `10⁻⁴` on 36 boxes, which satisfy the Y-bounds. -/

namespace Lean6.Special.D88.Boxes.KC

theorem counts_ok : kcCounts allData = some (1092, 3696, 36) := by native_decide

end Lean6.Special.D88.Boxes.KC
