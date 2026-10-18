import Lean6.Special.Comp.D98.RootsData

/-!
# Small facts about the root data (`native_decide`)
-/

namespace Lean6.Special.Comp.D98

theorem minFac_eq : minFac_1_2_7 = 3 ∧ minDisk_1_2_7 = 0 ∧ (disks_1_2_7.getD 3 ⟨0, []⟩).disks.length = 4 ∧
    0 ≤ minY_1_2_7.1 ∧ 0 ≤ minY_1_2_7.2 := by native_decide

end Lean6.Special.Comp.D98
