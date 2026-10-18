import CC6Compose.SpecialCore
import CC6Compose.EnumCore
import CC6Compose.ClassesLit
import L6Sound.F34S.Defs

/-!
# The open classes by kernel evaluation

`open_specials_lit`: the representatives in the literal class list `classes6Lit` of the classes with open cells have
the diagrams `specials`, checked by `decide +kernel`. The diagrams are compared by the membership of their finite sets
(`diagBEq`): the derived `DecidableEq` of `Diagram` transports along equalities of finite sets, which the kernel
reduces only when the underlying lists coincide. `OpenKernel.lean` derives the statement of `open_specials` from it.
-/

namespace CC6Compose

open CC6Full

/-- Equality of finite sets of a finite type by membership, as a Boolean. -/
def finsetBEq {α : Type} [Fintype α] [DecidableEq α] (s t : Finset α) : Bool :=
  decide (∀ a, a ∈ s ↔ a ∈ t)

theorem eq_of_finsetBEq {α : Type} [Fintype α] [DecidableEq α] {s t : Finset α} (h : finsetBEq s t = true) :
    s = t :=
  Finset.ext (of_decide_eq_true h)

/-- Equality of diagrams by the membership of their finite sets, as a Boolean. -/
def diagBEq (D E : Diagram 6) : Bool :=
  finsetBEq D.zStrokes E.zStrokes && finsetBEq D.wStrokes E.wStrokes && finsetBEq D.zCircles E.zCircles &&
    finsetBEq D.wCircles E.wCircles

theorem eq_of_diagBEq {D E : Diagram 6} (h : diagBEq D E = true) : D = E := by
  obtain ⟨zs, ws, zc, wc⟩ := D
  obtain ⟨zs', ws', zc', wc'⟩ := E
  simp only [diagBEq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [eq_of_finsetBEq h1, eq_of_finsetBEq h2, eq_of_finsetBEq h3, eq_of_finsetBEq h4]

/-- **The check, by kernel evaluation**: the representative in `classes6Lit` of each class with open cells has one
of the diagrams `specials`. -/
theorem open_specials_lit : ∀ k ∈ L6.F34S.openClasses, ∃ D ∈ specials,
    diagBEq (toDiagram (classes6Lit.getD k (default, 0)).1) D = true := by
  decide +kernel

end CC6Compose
