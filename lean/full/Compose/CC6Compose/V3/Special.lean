import CC6Compose.V3.Main
import CC6Compose.Dims
import CC6Compose.Seven

/-!
# The kernel-only composition: the statements consumed from `lean6_special`

`SpecialFacts` bundles the twelve statements of the certificate project of Sections 6 and 7 that the bridges use (Lemma
6.19(a)–(d), Lemma 7.9 over `𝔽_32003` and the fact at `(3, 5, 7, 11)` of §7.2), each as the type of the theorem of
`lean6_special` that proves it (for Lemma 7.9 the half over `𝔽_32003` of `lemma_7_9`, the only one the bridge uses:
Lemma 7.10 needs one prime). `sevenCerts'_of_facts` derives `SevenCerts'` from them through the bridges, on the standard
axioms; `specialFacts_native` is the instance from the theorems of `lean6_special` (checks run as compiled code). A
kernel version of `lean6_special` with the same statements gives `SpecialFacts` without them. `main_of_facts` is Theorem
1.1 from all the statements that the composition consumes.
-/

namespace CC6Compose.V3

open CC6Full CC6Full.Six

/-- The statements of `lean6_special` used by the bridges. -/
structure SpecialFacts : Prop where
  s12 : type_of% @Lean6.Special.D88.Count.count_S12
  kc : type_of% @Lean6.Special.D88.Count.count_KC
  box_c : type_of% @Lean6.Special.D88.Boxes.lemma_6_19_c
  box_d : type_of% @Lean6.Special.D88.Boxes.lemma_6_19_d
  n4_units : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok
  kc_units : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok
  n4_mem : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0}
  kc_mem : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0}
  n4_torus : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0}
  kc_torus : type_of% @Lean6.Special.D88.Trop.kc_torus_gamma.{0}
  c4 : Lean6.Special.K4.C4.NoZero [3, 5, 7, 11] 32003 ∧ Lean6.Special.K4.C4.UnitIdeal [3, 5, 7, 11] 32003
  e4 : type_of% @Lean6.Special.K4.E4.check_3_5_7_11

/-- **The computations of Sections 6 and 7** from the statements of `lean6_special`. -/
theorem sevenCerts'_of_facts (h : SpecialFacts) : SevenCerts' :=
  ⟨heavyFact, heavyFact3, e4NoZero_of h.e4, c4Cert_of h.c4, d88Int_of h.n4_units h.n4_mem h.n4_torus,
    d88Dim_of h.s12, d88Box_of h.box_c, d94Int_of h.kc_units h.kc_mem h.kc_torus, d94Dim_of h.kc, d94Box_of h.box_d⟩

/-- The statements of `lean6_special`, from its theorems. -/
theorem specialFacts_native : SpecialFacts :=
  ⟨Lean6.Special.D88.Count.count_S12, Lean6.Special.D88.Count.count_KC, Lean6.Special.D88.Boxes.lemma_6_19_c,
    Lean6.Special.D88.Boxes.lemma_6_19_d, Lean6.Special.Comp.D88.Trop.n4_units_ok,
    Lean6.Special.Comp.D88.Trop.kc_units_ok, Lean6.Special.D88.Trop.n4_G_mem, Lean6.Special.D88.Trop.kc_G_mem,
    Lean6.Special.D88.Trop.n4_torus_gamma, Lean6.Special.D88.Trop.kc_torus_gamma, Lean6.Special.K4.C4.lemma_7_9.1,
    Lean6.Special.K4.E4.check_3_5_7_11⟩

/-- **Theorem 1.1 from all the statements the composition consumes**: a class list with `F1Cover`,
`FusedExclusion` and `OpenCheck`, and the statements of `lean6_special`. On the standard axioms. -/
theorem main_of_facts (L : List (L6F1.Diagram × ℕ)) (hF1 : F1Cover L) (hF : FusedExclusion L) (hO : OpenCheck L)
    (h : SpecialFacts) : MainTheorem :=
  main_of_v3 L hF1 hF hO (sevenCerts'_of_facts h)

end CC6Compose.V3
