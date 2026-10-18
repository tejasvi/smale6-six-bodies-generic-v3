import CC6Compose.V3.Kernel
import L6CheckTrop.N4.Final
import Lean6.Special.D88.Count.Main

/-!
# Theorem 1.1, version 3

Version 3 checks every computation of the paper in the kernel except the two dimension bounds of Lemma 6.19(b), which
come from `lean6_special`'s `count_S12` and `count_KC` (Gröbner bases computed by an F4 implementation run as compiled
code). Everything else enters through the kernel versions assembled in `Kernel.lean`, and the torus statement of `N4`
(Lemma 6.19(a)) through its kernel version `Lean6.Special.D88.TropK.n4_torus_gamma`.

`main_theorem_v3`: Theorem 1.1. Its axioms are `propext`, `Classical.choice`, `Quot.sound` and the two auxiliary axioms
of the F4 runs behind `count_S12` and `count_KC` (`Compose/CheckV3.lean`). `main_theorem_v3_of`, `main_theorem_v3_of3`,
`main_theorem_v3_of1`: Theorem 1.1 from the statements of Lemma 6.19(a) that had no kernel version yet when they were
written: the membership identities `n4_G_mem`, `kc_G_mem` and the torus statements `n4_torus_gamma`,
`kc_torus_gamma`; then `kc_torus_gamma` from its kernel version (`Lean6.Special.D88.TropK.kc_torus_gamma`); then also
the membership identities from their kernel versions, so that only the torus statement of `N4` remained.
-/

namespace CC6Compose.V3

open CC6Full

/-- **Theorem 1.1 (version 3), from the four statements of Lemma 6.19(a) without a kernel version yet.** -/
theorem main_theorem_v3_of (n4m : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0})
    (kcm : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0})
    (n4t : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0})
    (kct : type_of% @Lean6.Special.D88.Trop.kc_torus_gamma.{0}) : MainTheorem :=
  main_theorem_k_of6 Lean6.Special.D88.Count.count_S12 Lean6.Special.D88.Count.count_KC n4m kcm n4t kct

/-- **Theorem 1.1 (version 3), from the three statements of Lemma 6.19(a) without a kernel version yet.** -/
theorem main_theorem_v3_of3 (n4m : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0})
    (kcm : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0})
    (n4t : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0}) : MainTheorem :=
  main_theorem_k_of5 Lean6.Special.D88.Count.count_S12 Lean6.Special.D88.Count.count_KC n4m kcm n4t

/-- **Theorem 1.1 (version 3), from the torus statement of `N4`**, the one statement of Lemma 6.19(a) without a kernel
version yet. -/
theorem main_theorem_v3_of1 (n4t : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0}) : MainTheorem :=
  main_theorem_k_of3 Lean6.Special.D88.Count.count_S12 Lean6.Special.D88.Count.count_KC n4t

/-- **Theorem 1.1 (version 3).** -/
theorem main_theorem_v3 : MainTheorem :=
  main_theorem_v3_of1 Lean6.Special.D88.TropK.n4_torus_gamma

end CC6Compose.V3
