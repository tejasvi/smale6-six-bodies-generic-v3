import CC6Compose.V3.Special
import L6CheckF.Final
import L6CheckK.F1.Main
import L6CheckKSpec.Final
import L6CheckKSpec.E4Final
import L6CheckC4.Final
import L6CheckKSpec.TropUnits
import L6CheckTrop.KC.Final
import L6CheckKSpec.TropMem

/-!
# The kernel-only composition: the instances from the kernel checks

The hypotheses of `main_of_facts` for the literal class list `L6CheckK.F1.classes6L` of the kernel version of the
certificate project: `F1Cover` from `L6CheckK.F1.F1_main_k`, `FusedExclusion` from `L6CheckF.fusedK` (the
certificates from `L6CheckF.csAll`), `OpenCheck` by kernel evaluation. `main_theorem_k_of`: Theorem 1.1 from the
statements of `lean6_special` alone; `main_theorem_k_of9`: the same with Lemma 6.19(c), (d) and the fact at
`(3, 5, 7, 11)` from their kernel versions (`Lean6.Special.D88.BoxesK`, `Lean6.Special.K4.E4K`), so that nine
statements of `lean6_special` remain as hypotheses; `main_theorem_k_of8`: also Lemma 7.9 over `𝔽_32003` from its
kernel version (`L6CheckC4.lemma_7_9_32003`), so that the eight statements of Lemma 6.19(a), (b) remain;
`main_theorem_k_of6`: also the coefficient checks of Lemma 6.19(a) (`Lean6.Special.Comp.D88.TropK.n4_units_ok`,
`kc_units_ok`), so that six remain; `main_theorem_k_of5`: also the torus statement of `KC₁₂`
(`Lean6.Special.D88.TropK.kc_torus_gamma`), so that five remain; `main_theorem_k_of3`: also the membership identities
of Lemma 6.19(a) (`Lean6.Special.D88.TropK.n4_G_mem`, `kc_G_mem`), so that the two counts of Lemma 6.19(b) and the
torus statement of `N4` remain.
-/

namespace CC6Compose.V3

open CC6Full
open L6.F2S (ExpTree Cond)

theorem itemOK_of_itemOKK {Xz Xw : ExpTree} {it : L6.F34S.ItemX} (h : L6K.F34K.ItemOKK Xz Xw it) :
    ItemOK Xz Xw it := by
  cases it <;> exact h

theorem claimMeaningIn_of_K {cs : List L6.Poly.Cert} {Xz Xw : ExpTree}
    (h : L6K.F34K.ClaimMeaningFinK cs Xz Xw) : ClaimMeaningIn cs Xz Xw := by
  rcases h with hs | ⟨c, hc, vars, hmean, hF6, hsz, hgen⟩
  · exact Or.inl hs
  · exact Or.inr ⟨c, hc, vars, hmean, hF6, hsz, fun j hj =>
      (hgen j hj).imp fun it hit => ⟨itemOK_of_itemOKK hit.1, hit.2⟩⟩

theorem f1Cover_K : F1Cover L6CheckK.F1.classes6L := by
  obtain ⟨-, -, hlen, hcls, -⟩ := L6CheckK.F1.F1_main_k
  exact ⟨hlen, fun d hd hok => (hcls d).mp ⟨hd, hok⟩⟩

theorem fused_K : FusedExclusion L6CheckK.F1.classes6L := by
  intro k hk
  refine ⟨L6CheckF.csAll, fun Xz Xw hX => ?_⟩
  exact (L6CheckF.fusedK k hk Xz Xw hX).imp id claimMeaningIn_of_K

theorem openCheck_K : OpenCheck L6CheckK.F1.classes6L := by
  unfold OpenCheck
  decide +kernel

/-- **Theorem 1.1 from the statements of `lean6_special`**, everything else by kernel evaluation. -/
theorem main_theorem_k_of (h : SpecialFacts) : MainTheorem :=
  main_of_facts L6CheckK.F1.classes6L f1Cover_K fused_K openCheck_K h

/-- **Theorem 1.1 from the nine statements of `lean6_special` without a kernel version yet**: Lemma 6.19(c), (d) and
the fact at `(3, 5, 7, 11)` come from their kernel versions. -/
theorem main_theorem_k_of9 (s12 : type_of% @Lean6.Special.D88.Count.count_S12)
    (kc : type_of% @Lean6.Special.D88.Count.count_KC)
    (n4u : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok)
    (kcu : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok)
    (n4m : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0}) (kcm : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0})
    (n4t : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0})
    (kct : type_of% @Lean6.Special.D88.Trop.kc_torus_gamma.{0})
    (c4 : Lean6.Special.K4.C4.NoZero [3, 5, 7, 11] 32003 ∧ Lean6.Special.K4.C4.UnitIdeal [3, 5, 7, 11] 32003) :
    MainTheorem :=
  main_theorem_k_of ⟨s12, kc, Lean6.Special.D88.BoxesK.lemma_6_19_c, Lean6.Special.D88.BoxesK.lemma_6_19_d, n4u, kcu,
    n4m, kcm, n4t, kct, c4, Lean6.Special.K4.E4K.check_3_5_7_11⟩

/-- **Theorem 1.1 from the eight statements of Lemma 6.19(a), (b)**: Lemma 6.19(c), (d), the fact at `(3, 5, 7, 11)`
and Lemma 7.9 over `𝔽_32003` come from their kernel versions. -/
theorem main_theorem_k_of8 (s12 : type_of% @Lean6.Special.D88.Count.count_S12)
    (kc : type_of% @Lean6.Special.D88.Count.count_KC)
    (n4u : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok)
    (kcu : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok)
    (n4m : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0}) (kcm : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0})
    (n4t : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0})
    (kct : type_of% @Lean6.Special.D88.Trop.kc_torus_gamma.{0}) : MainTheorem :=
  main_theorem_k_of9 s12 kc n4u kcu n4m kcm n4t kct L6CheckC4.lemma_7_9_32003

/-- **Theorem 1.1 from the six statements of Lemma 6.19(a) (membership identities, torus statements) and (b)**: the
coefficient checks of Lemma 6.19(a) come from their kernel versions as well. -/
theorem main_theorem_k_of6 (s12 : type_of% @Lean6.Special.D88.Count.count_S12)
    (kc : type_of% @Lean6.Special.D88.Count.count_KC)
    (n4m : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0}) (kcm : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0})
    (n4t : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0})
    (kct : type_of% @Lean6.Special.D88.Trop.kc_torus_gamma.{0}) : MainTheorem :=
  main_theorem_k_of8 s12 kc Lean6.Special.Comp.D88.TropK.n4_units_ok Lean6.Special.Comp.D88.TropK.kc_units_ok n4m kcm
    n4t kct

/-- **Theorem 1.1 from the five statements without a kernel version yet**: the counts of Lemma 6.19(b), the
membership identities of Lemma 6.19(a) and the torus statement of `N4`; the torus statement of `KC₁₂` comes from its
kernel version as well. -/
theorem main_theorem_k_of5 (s12 : type_of% @Lean6.Special.D88.Count.count_S12)
    (kc : type_of% @Lean6.Special.D88.Count.count_KC)
    (n4m : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0}) (kcm : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0})
    (n4t : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0}) : MainTheorem :=
  main_theorem_k_of6 s12 kc n4m kcm n4t Lean6.Special.D88.TropK.kc_torus_gamma

/-- **Theorem 1.1 from the two counts of Lemma 6.19(b) and the torus statement of `N4`**: the membership identities
of Lemma 6.19(a) come from their kernel versions as well. -/
theorem main_theorem_k_of3 (s12 : type_of% @Lean6.Special.D88.Count.count_S12)
    (kc : type_of% @Lean6.Special.D88.Count.count_KC)
    (n4t : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0}) : MainTheorem :=
  main_theorem_k_of5 s12 kc Lean6.Special.D88.TropK.n4_G_mem Lean6.Special.D88.TropK.kc_G_mem n4t

end CC6Compose.V3
