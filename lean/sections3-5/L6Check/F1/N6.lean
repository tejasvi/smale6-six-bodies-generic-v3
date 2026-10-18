import L6F1

/-!
# Proposition 3.1 for six bodies: the computation

`checkAll 6 false n6json 932677 82712 191` (see `L6F1.Check`), evaluated as compiled code by `native_decide`: the
edge stage leaves 932,677 kind assignments; the search finds 82,712 labelled diagrams, distinct, each satisfying the
rules; the class file `n6.json` is read and written back identically and lists 191 classes whose orbits are exactly
the labelled diagrams found, with the listed sizes, each representative having the least key (`rawKey`) of its orbit,
in increasing order of the keys.
-/

namespace L6F1

set_option profiler true in
/-- The checks of Proposition 3.1 for six bodies. -/
theorem check_n6 : checkAll 6 false n6json 932677 82712 191 = true := by native_decide

end L6F1
