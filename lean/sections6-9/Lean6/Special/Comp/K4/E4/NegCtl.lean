import Lean6.Special.Comp.K4.E4.Rem

/-!
# Negative controls for the Macaulay check (not imported by the library)

The check must fail where the forms have a common zero: (1) the first three patterns of Remark 7.14 at
`μ = (1, 1, 1, 2)` to which the construction applies; (2) the forms `F_ε` at `μ = (1, 1, 1, 1)`, `e = 0`, without the
cubic `Σ μ_k q_k³` (common zero `q = (1, 1, 1, 1)`); (3) the exact test of an inverse rejects a wrong one.
-/

namespace Lean6.Special.Comp.E4

theorem negctl_rem :
    ((patsG.filter (consApplies [1, 1, 1, 2])).take 3).map (fun w => macCheck 3 8 pE sE (formsG [1, 1, 1, 2] w)) =
      [false, false, false] := by native_decide

theorem negctl_F : macCheck 4 7 pE sE ((formsF [1, 1, 1, 1] [0, 0, 0, 0, 0, 0]).take 6) = false := by native_decide

theorem negctl_inv : verifyInv pE 2 #[#[1, 1], #[0, 1]] #[#[1, 0], #[0, 1]] = false := by native_decide

end Lean6.Special.Comp.E4
