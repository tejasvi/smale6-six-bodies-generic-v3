import CC6Full.Interface

/-!
# The seven diagrams of Sections 6 and 7 in the labelling of the classification

The classification (`reps6`, from the diagram checker) uses its own representatives; seven of them are images of the
diagrams of Table 1 under a relabelling, possibly followed by the exchange of the colours: the representatives of the
classes `124, 143, 127, 31, 132, 147, 133` of the checker's list are the images of diagrams `64, 66, 88, 89, 93, 94, 98`.
`specials` lists these images (computed here from Table 1), and `specials_excluded` excludes their germs at generic
masses from `SevenCerts'` (Sections 6 and 7), by the invariance of `DiagExcluded` (`DiagExcluded.relabel_cond`).
-/

namespace CC6Compose

open CC6Full

/-- The permutation of `Fin 6` given by the list of its values. -/
def permOf (f g : Fin 6 → Fin 6) (h1 : ∀ i, g (f i) = i) (h2 : ∀ i, f (g i) = i) : Equiv.Perm (Fin 6) :=
  ⟨f, g, h1, h2⟩

/-- The image of a diagram under a relabelling followed, if `b`, by the exchange of the colours. -/
def img (D : Diagram 6) (σ : Equiv.Perm (Fin 6)) (b : Bool) : Diagram 6 :=
  bif b then (D.relabel σ).swap else D.relabel σ

def σ64 : Equiv.Perm (Fin 6) := permOf ![0, 2, 3, 4, 5, 1] ![0, 5, 1, 2, 3, 4] (by decide) (by decide)
def σ66 : Equiv.Perm (Fin 6) := permOf ![0, 2, 3, 4, 1, 5] ![0, 4, 1, 2, 3, 5] (by decide) (by decide)
def σ88 : Equiv.Perm (Fin 6) := permOf ![4, 0, 1, 2, 3, 5] ![1, 2, 3, 4, 0, 5] (by decide) (by decide)
def σ89 : Equiv.Perm (Fin 6) := permOf ![0, 1, 4, 5, 2, 3] ![0, 1, 4, 5, 2, 3] (by decide) (by decide)
def σ93 : Equiv.Perm (Fin 6) := permOf ![0, 3, 4, 5, 1, 2] ![0, 4, 5, 1, 2, 3] (by decide) (by decide)
def σ94 : Equiv.Perm (Fin 6) := permOf ![4, 0, 1, 2, 5, 3] ![1, 2, 3, 5, 0, 4] (by decide) (by decide)
def σ98 : Equiv.Perm (Fin 6) := permOf ![0, 3, 4, 5, 1, 2] ![0, 4, 5, 1, 2, 3] (by decide) (by decide)

/-- The images of the seven diagrams of Table 1 that are representatives of the classification. -/
def specials : List (Diagram 6) :=
  [img Diagram.d64 σ64 false, img Diagram.d66 σ66 false, img Diagram.d88 σ88 true, img Diagram.d89 σ89 false,
    img Diagram.d93 σ93 false, img Diagram.d94 σ94 true, img Diagram.d98 σ98 false]

/-- **Sections 6 and 7** for the representatives of the classification. -/
theorem specials_excluded (h : SevenCerts') : ∀ D ∈ specials, DiagExcluded D := by
  obtain ⟨h89, h98, h93, h64, h66, h88, h94⟩ := seven_excluded' h
  intro D hD
  simp only [specials, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h64.relabel_cond (Diagram.ordered_ofLists _ _ _ _) _ _
  · exact h66.relabel_cond (Diagram.ordered_ofLists _ _ _ _) _ _
  · exact h88.relabel_cond (Diagram.ordered_ofLists _ _ _ _) _ _
  · exact h89.relabel_cond (Diagram.ordered_ofLists _ _ _ _) _ _
  · exact h93.relabel_cond (Diagram.ordered_ofLists _ _ _ _) _ _
  · exact h94.relabel_cond (Diagram.ordered_ofLists _ _ _ _) _ _
  · exact h98.relabel_cond (Diagram.ordered_ofLists _ _ _ _) _ _

end CC6Compose
