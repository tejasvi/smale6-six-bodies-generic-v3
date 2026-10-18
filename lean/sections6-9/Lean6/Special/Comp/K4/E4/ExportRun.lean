import Lean6.Special.Comp.K4.E4.Export

/-!
# The export checks (compiled runs)

For all 729 patterns `ε` and all 64 sign patterns `σ`: the unit-mass Macaulay rows are the sums of their listed terms,
and the coefficient matrices at `μ₀ = (3, 5, 7, 11)` and at `(1, 1, 1, 1)` are the combinations of the unit-mass
matrices (`Export`).
-/

namespace Lean6.Special.Comp.E4

theorem monosOK_ok : monosOK = true := by native_decide

theorem exportF_ok : patsF.all (exportF [[3, 5, 7, 11], [1, 1, 1, 1]]) = true := by native_decide

theorem exportG_ok : patsG.all (exportG [[3, 5, 7, 11], [1, 1, 1, 1]]) = true := by native_decide

end Lean6.Special.Comp.E4
