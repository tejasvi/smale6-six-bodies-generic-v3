import CC6Full.Main
import CC6Full.Classes
import CC6Full.Six.D89
import CC6Full.Six.D98
import CC6Full.Six.D93
import CC6Full.Six.D64Poly
import CC6Full.Six.D64NoZero
import CC6Full.Six.D66Poly
import CC6Full.Six.D88
import CC6Full.Six.D94

/-!
# What remains: the interface between the proved theory and the certificate checkers

Theorem 1.1 is proved here from two groups of statements that the sibling certificate projects check by
computation, and that will be connected by bridge lemmas.

* `SevenCerts`: the computations used for the seven diagrams of Sections 6 and 7 at one mass point each:
  the heavy-mass facts of Lemma 6.13 (`HeavyFact`, `HeavyFact3`, at `(1, 2, 40)`), the Macaulay certificate of §7.2
  (`E4Cert`, at `(3, 5, 7, 11)`), the chart certificate of Lemma 7.9 (`C4Cert`), and for diagrams 88 and 94 the
  integrality of Lemma 6.18, the dimension bound of Lemma 6.19(b) and the boxes of Lemma 6.19(c), (d).
* `ClassesExcluded`: the classification of Proposition 3.1 (every diagram of a germ is, up to relabelling and the
  exchange of the colours, one of finitely many ordered representatives) together with the exclusion of the germs of
  each representative with `ℓ ≤ 0` (Propositions 4.5 and 5.3 for the cells, and Sections 6 and 7 for the seven
  diagrams, through `seven_excluded`).

`seven_excluded` proves the exclusion of the germs of the seven diagrams of Table 1 from `SevenCerts`, and
`main_of_classesExcluded` proves `MainTheorem` from `ClassesExcluded`.
-/

namespace CC6Full

open Six

/-- The computations at one mass point used by Sections 6 and 7. -/
def SevenCerts : Prop :=
  HeavyFact ∧ HeavyFact3 ∧ E4Cert ∧ C4Cert ∧ D88Int ∧ D88Dim ∧ D88Box ∧ D94Int ∧ D94Dim ∧ D94Box

/-- **Sections 6 and 7**: the germs with one of the seven diagrams of Table 1 are excluded at generic masses
(Theorems 6.5, 6.12, 6.15, 6.20, 7.12, 7.13). -/
theorem seven_excluded (h : SevenCerts) :
    DiagExcluded Diagram.d89 ∧ DiagExcluded Diagram.d98 ∧ DiagExcluded Diagram.d93 ∧
      DiagExcluded Diagram.d64 ∧ DiagExcluded Diagram.d66 ∧ DiagExcluded Diagram.d88 ∧
        DiagExcluded Diagram.d94 := by
  obtain ⟨hH, hH3, hE, hC, h88i, h88d, h88b, h94i, h94d, h94b⟩ := h
  exact ⟨DiagExcluded.of_no_germ fun m hm G => d89_excluded hm G,
    DiagExcluded.of_exists_poly (d98_poly hH), DiagExcluded.of_exists_poly (d93_poly hH3),
    DiagExcluded.of_exists_poly (d64_poly hE), DiagExcluded.of_exists_poly (d66_poly hC),
    DiagExcluded.of_exists_poly (d88_poly h88i h88d h88b),
    DiagExcluded.of_exists_poly (d94_poly h94i h94d h94b)⟩

/-- `SevenCerts` with the no-zero form of the check at `(3, 5, 7, 11)` of §7.2 (`E4NoZero`, the form proved by the
certificate project) in place of the Macaulay minors (`E4Cert`). -/
def SevenCerts' : Prop :=
  HeavyFact ∧ HeavyFact3 ∧ E4NoZero ∧ C4Cert ∧ D88Int ∧ D88Dim ∧ D88Box ∧ D94Int ∧ D94Dim ∧ D94Box

/-- **Sections 6 and 7** from `SevenCerts'`. -/
theorem seven_excluded' (h : SevenCerts') :
    DiagExcluded Diagram.d89 ∧ DiagExcluded Diagram.d98 ∧ DiagExcluded Diagram.d93 ∧
      DiagExcluded Diagram.d64 ∧ DiagExcluded Diagram.d66 ∧ DiagExcluded Diagram.d88 ∧
        DiagExcluded Diagram.d94 := by
  obtain ⟨hH, hH3, hE, hC, h88i, h88d, h88b, h94i, h94d, h94b⟩ := h
  exact ⟨DiagExcluded.of_no_germ fun m hm G => d89_excluded hm G,
    DiagExcluded.of_exists_poly (d98_poly hH), DiagExcluded.of_exists_poly (d93_poly hH3),
    DiagExcluded.of_exists_poly (d64_poly_of_noZero hE), DiagExcluded.of_exists_poly (d66_poly hC),
    DiagExcluded.of_exists_poly (d88_poly h88i h88d h88b),
    DiagExcluded.of_exists_poly (d94_poly h94i h94d h94b)⟩

/-- The classification of the diagrams of germs and the exclusion of each class. -/
def ClassesExcluded : Prop :=
  ∃ reps : Finset (Diagram 6), (∀ D ∈ reps, D.Ordered) ∧
    (∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, ∃ D ∈ reps, ∃ σ : Equiv.Perm (Fin 6), ∃ b : Bool,
      G.HasDiagram (bif b then (D.relabel σ).swap else D.relabel σ)) ∧
    ∀ D ∈ reps, DiagExcluded D

/-- **Theorem 1.1** from the classification and the exclusion of the classes. -/
theorem main_of_classesExcluded (h : ClassesExcluded) : MainTheorem := by
  obtain ⟨reps, hord, hcls, hexc⟩ := h
  exact main_of_germExclusion (germExclusion_of_classes reps hord hcls hexc)

end CC6Full
