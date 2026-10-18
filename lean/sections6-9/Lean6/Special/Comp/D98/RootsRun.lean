import Lean6.Special.Comp.D98.RootsData

/-!
# The runs of the root disks (`native_decide`)

`roots_1_2_7`: the disks of the eight factors of `S_μ` at `μ = (1,2,7)` pass `rootsOK` with `θ = 0.7641079385`;
`upper_1_2_7`: on the disk of the smallest `ρ` (a root of `N₁₁`), `ρ ≤ 0.7641079386`; `roots_1_2_8`: the same at
`μ = (1,2,8)` with `θ = 0.7990358445`.
-/

namespace Lean6.Special.Comp.D98

theorem roots_1_2_7 : rootsOK 1 2 7 (7641079385 / 10000000000) disks_1_2_7 = true := by native_decide

theorem roots_1_2_8 : rootsOK 1 2 8 (7990358445 / 10000000000) disks_1_2_8 = true := by native_decide

theorem upper_1_2_7 :
    upperOK 1 2 7 (7641079386 / 10000000000) (1 / (2 : Rat) ^ ((disks_1_2_7.getD minFac_1_2_7 ⟨0, []⟩).m))
      ((disks_1_2_7.getD minFac_1_2_7 ⟨0, []⟩).disks.getD minDisk_1_2_7 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)
      minY_1_2_7.1.toNat minY_1_2_7.2.toNat = true := by native_decide

end Lean6.Special.Comp.D98
