import CC6Compose.Special
import CC6Compose.Exclusion

/-!
# Theorem 1.1 from the dimension bounds of Lemma 6.19(b)

`open_specials`: the representatives of the seven classes with open cells (the classes `31, 124, 127, 132, 133, 143,
147` of the classification, `L6.F34S.openClasses`) are the images of the diagrams of Table 1 listed in `specials`
(a computation on the class file). With `diagExcluded_of_mem` (Propositions 4.5 and 5.3 for the other classes) this
gives the hypothesis `hcells` of `main_of`, and `main_of_dims` proves Theorem 1.1 from the two dimension bounds of
Lemma 6.19(b), which `Dims.lean` proves (`main_theorem` in `Theorem.lean`).
-/

namespace CC6Compose

open CC6Full

/-- The representatives of the classes with open cells are the images of the diagrams of Table 1. -/
theorem open_specials : ∀ k ∈ L6.F34S.openClasses,
    toDiagram (L6F1.classes6.getD k (default, 0)).1 ∈ specials := by
  native_decide

/-- **Propositions 4.5 and 5.3**: the germs of the representatives other than the seven of Sections 6 and 7 are
excluded at generic masses. -/
theorem hcells : ∀ D ∈ reps6, D ∉ specials → DiagExcluded D := by
  intro D hD hns
  obtain ⟨x, hx, rfl⟩ := mem_reps6.mp hD
  refine diagExcluded_of_mem hx fun hopen => hns ?_
  have h := open_specials _ hopen
  have hlt : L6F1.classes6.idxOf x < L6F1.classes6.length := List.idxOf_lt_length_iff.mpr hx
  rwa [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt] at h

/-- **Theorem 1.1** from the dimension bounds of Lemma 6.19(b). -/
theorem main_of_dims (h88d : Six.D88Dim) (h94d : Six.D94Dim) : MainTheorem :=
  main_of h88d h94d hcells

end CC6Compose
