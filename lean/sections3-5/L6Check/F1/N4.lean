import L6F1

/-!
# The check for four bodies

`checkAll 4 true n4json 633 41 5`: the edge stage leaves 633 kind assignments; the search finds 41 labelled diagrams,
each satisfying the rules; `n4.json` lists 5 classes whose orbits are exactly these diagrams, ordered by the
lexicographic key of the files for four and five bodies (`rawKeyLex`).
-/

namespace L6F1

set_option profiler true in
/-- The checks of the search for four bodies. -/
theorem check_n4 : checkAll 4 true n4json 633 41 5 = true := by native_decide

end L6F1
