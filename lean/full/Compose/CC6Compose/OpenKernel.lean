import CC6Compose.OpenCore
import CC6Compose.Final

/-!
# `open_specials` by kernel evaluation

`open_specials` (`Final.lean`) is proved by `native_decide`. Here its statement follows from the kernel-evaluated check
`open_specials_lit` (`OpenCore.lean`) on the literal `classes6Lit`, given the equation `L6F1.classes6 = classes6Lit`
(`open_specials_of_eq`; `classes6_eq_of_parse` gives the equation from the reading of `n6.json`).
-/

namespace CC6Compose

open CC6Full

/-- **`open_specials` from the equation `L6F1.classes6 = classes6Lit`**. -/
theorem open_specials_of_eq (hL : L6F1.classes6 = classes6Lit) : ∀ k ∈ L6.F34S.openClasses,
    toDiagram (L6F1.classes6.getD k (default, 0)).1 ∈ specials := by
  intro k hk
  obtain ⟨D, hD, h⟩ := open_specials_lit k hk
  rw [hL, eq_of_diagBEq h]
  exact hD

/-- The equation `L6F1.classes6 = classes6Lit` from the reading of `n6.json`. -/
theorem classes6_eq_of_parse (h : L6F1.parseFile L6F1.n6json = some (6, 82712, classes6Lit)) :
    L6F1.classes6 = classes6Lit := by
  unfold L6F1.classes6
  exact L6F1.classesOf_eq h

end CC6Compose
