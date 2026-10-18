import L6F1

/-!
# The check for five bodies

`checkAll 5 true n5json 18918 1376 24`: the edge stage leaves 18,918 kind assignments; the search finds 1376 labelled
diagrams, each satisfying the rules; `n5.json` lists 24 classes whose orbits are exactly these diagrams, ordered by the
lexicographic key of the files for four and five bodies (`rawKeyLex`).
-/

namespace L6F1

set_option profiler true in
/-- The checks of the search for five bodies. -/
theorem check_n5 : checkAll 5 true n5json 18918 1376 24 = true := by native_decide

end L6F1
