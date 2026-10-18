import Lean6.Special.Comp.K4.E4.Mac

/-!
# The Macaulay checks of §7.2 (compiled runs)

At `μ = (1, 1, 1, 1)` (Lemma 7.7) and at `μ₀ = (3, 5, 7, 11)` (the check after Proposition 7.8): for all 729 patterns
`ε` the Macaulay matrix of `F_ε` in degree 7, and for all 64 patterns `σ` that of `G_σ` in degree 8, has a selected
square block invertible modulo `p = 2147483629`, with `j ↦ 882503254` (`s = 2j + 1 ↦ 1765006509`, `s² ≡ −3`).
-/

namespace Lean6.Special.Comp.E4

/-- The prime of the paper. -/
abbrev pE : Nat := 2147483629

/-- The root of `t² + t + 1` modulo `pE` of the paper. -/
abbrev rE : Nat := 882503254

/-- `s = 2 rE + 1`, a square root of `−3` modulo `pE`. -/
abbrev sE : Nat := 2 * rE + 1

theorem rE_root : (rE * rE + rE + 1) % pE = 0 := by decide

theorem sE_sq : (sE * sE + 3) % pE = 0 := by decide

theorem allF_1111 : allF [1, 1, 1, 1] pE sE = true := by native_decide

theorem allG_1111 : allG [1, 1, 1, 1] pE sE = true := by native_decide

theorem allF_3_5_7_11 : allF [3, 5, 7, 11] pE sE = true := by native_decide

theorem allG_3_5_7_11 : allG [3, 5, 7, 11] pE sE = true := by native_decide

end Lean6.Special.Comp.E4
