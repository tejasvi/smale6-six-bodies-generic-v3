import L6K.F34K.Check

/-!
# Argmin sets without repetition

The test, evaluated by the kernel on the claims of a unit beside `checkCells`, that the argmin set of every item of a
core has no repetition (`claimNodupB`): Lemma 5.2 reads the value of an item as its initial form, which needs it.
-/

namespace L6K.F34K

/-- `l` has no repetition. -/
def nodupB : List Nat → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

/-- The argmin sets of the items of a claim have no repetition. -/
def claimNodupB : ClaimK → Bool
  | .single .. => true
  | .core _ _ _ _ _ items => items.all fun it => nodupB it.S

end L6K.F34K
