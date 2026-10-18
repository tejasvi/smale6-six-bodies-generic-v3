import L6F2S.Search
import L6F2.Check

/-!
# The insertion orders list the six bodies

For each of the 191 classes, the insertion order of the bodies of its representative is a permutation of the six
bodies: the hypothesis `hord` of `search_complete` and `cells_sound`.
-/

namespace L6.F2S.Checks

open L6.F2S

/-- The insertion order of every class lists the six bodies. -/
theorem f2s_order : ∀ k < 191, (order (L6.F2.diagOf k)).Perm (List.range 6) := by
  native_decide

end L6.F2S.Checks
