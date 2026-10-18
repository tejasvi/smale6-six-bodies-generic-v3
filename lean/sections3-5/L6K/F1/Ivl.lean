import L6K.F1.SortR
import L6F1.Search

/-!
# The global comparison of codes, by intervals

The 82,712 codes of the shards and the orbit codes of the classes are compared interval by interval (one theorem per
interval, so that no kernel declaration holds all the codes): on each interval `[lo, hi)` (`hi = 0`: no upper end)
the sorted codes of the shards are strictly increasing and equal to the sorted orbit codes in that interval.
`chainOK` checks that the intervals cover the natural numbers.
-/

namespace L6K.F1

/-- `lo ≤ c < hi`, with `hi = 0` for no upper end. -/
def inIvl (lo hi c : Nat) : Bool := decide (lo ≤ c) && (hi == 0 || decide (c < hi))

/-- The intervals start at `lo`, each ends where the next starts, and the last has no upper end. -/
def chainOK : Nat → List (Nat × Nat) → Bool
  | _, [] => false
  | lo, [(a, b)] => a == lo && b == 0
  | lo, (a, b) :: rest => a == lo && decide (a < b) && chainOK b rest

/-- On `[lo, hi)`: the sorted codes of `C` are strictly increasing and equal to the sorted codes of `R`. -/
noncomputable def ivlCheck (C R : List Nat) (lo hi : Nat) : Bool :=
  L6F1.strictSorted (msortR 20 (C.filter (inIvl lo hi))) &&
    msortR 20 (C.filter (inIvl lo hi)) == msortR 20 (R.filter (inIvl lo hi))

end L6K.F1
