import L6KSpec.Boxes

/-!
# The classification of the KC boxes for the kernel

`kcClassB`, `kcCountsB`: `kcClass`, `kcCounts` of lean6_special on `Box` values instead of strings (no parsing).
-/

namespace L6KSpec

open Lean6.Special.D88.Boxes

/-- The classification of a KC box (`kcClass` after parsing): `(T-test over 1, 2, 3 passes, margin below 10⁻⁴)`;
`none` if a decision fails or if the margin is below `10⁻⁴` without the Y-bounds. -/
def kcClassB (b : Box) : Option (Bool × Bool) :=
  match t123Decide b, smallDecide b with
  | some t, some sm => if sm && !yBounds b then none else some (t, sm)
  | _, _ => none

/-- One step of the counts: the class of a box added to the counts of the rest. -/
def countStep : Option (Bool × Bool) → Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat)
  | some (t, sm), some (f, p, k) => some (f + (if t then 0 else 1), p + (if t then 1 else 0), k + (if sm then 1 else 0))
  | _, _ => none

/-- The counts `(#fail, #pass, #small)` over a list of boxes (`kcCounts` after parsing; `none` if a box is undecided). -/
def kcCountsB : List Box → Option (Nat × Nat × Nat)
  | [] => some (0, 0, 0)
  | b :: rest => countStep (kcClassB b) (kcCountsB rest)

/-- The sum of two counts. -/
def addCounts : Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat)
  | some (f, p, k), some (f', p', k') => some (f + f', p + p', k + k')
  | _, _ => none

end L6KSpec
