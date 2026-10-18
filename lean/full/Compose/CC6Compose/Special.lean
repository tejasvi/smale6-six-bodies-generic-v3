import CC6Compose.SpecialCore
import CC6Compose.Seven
import CC6Compose.Enum

/-!
# Theorem 1.1 from the classification, the seven diagrams and the cells

`main_of`: Theorem 1.1 from the dimension bounds of Lemma 6.19(b) and the exclusion of the germs of the
representatives of the classification other than the seven diagrams of Sections 6 and 7 (`specials`,
`specials_excluded` in `SpecialCore.lean`).
-/

namespace CC6Compose

open CC6Full

/-- **Theorem 1.1**, from the dimension bounds of Lemma 6.19(b) and the exclusion of the germs of the representatives
of the classification other than the seven of Sections 6 and 7 (Propositions 4.5 and 5.3). -/
theorem main_of (h88d : Six.D88Dim) (h94d : Six.D94Dim)
    (hcells : ∀ D ∈ reps6, D ∉ specials → DiagExcluded D) : MainTheorem := by
  refine main_of_classesExcluded (classesExcluded_of fun D hD => ?_)
  by_cases hs : D ∈ specials
  · exact specials_excluded (sevenCerts'_of h88d h94d) D hs
  · exact hcells D hD hs

end CC6Compose
