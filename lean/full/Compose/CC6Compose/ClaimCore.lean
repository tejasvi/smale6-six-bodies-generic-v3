import L6Sound.F34S.Defs

/-!
# The items of a claim

`ItemOK Xz Xw it`: the item holds at `(Xz, Xw)` (`L6.F34S.ItemX.Holds`), and the argmin set of an initial form has no
repetition, which Lemma 5.2 needs (`core_vanish`). Used by the claims of the native checks (`ExclusionClaim.lean`)
and by the string-free statements (`V3/Interface.lean`).
-/

namespace CC6Compose

open L6.F2S (ExpTree)
open L6.F34S (ItemX)

/-- The item holds at `(Xz, Xw)`, and the argmin set of an initial form has no repetition. -/
def ItemOK (Xz Xw : ExpTree) : ItemX → Prop
  | .init I S => (ItemX.init I S).Holds Xz Xw ∧ S.Nodup
  | .dist k l => (ItemX.dist k l).Holds Xz Xw

end CC6Compose
