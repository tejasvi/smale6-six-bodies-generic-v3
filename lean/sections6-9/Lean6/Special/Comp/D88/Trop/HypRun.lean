import Lean6.Special.Comp.D88.Trop.RunN4
import Lean6.Special.Comp.D88.Trop.RunKC
import Lean6.Special.Comp.K4.C4.GB

/-!
# Lemma 6.19(a): the two systems on the escape ray, by the Buchberger engine (`native_decide`)

The coverings of `RunN4`, `RunKC` leave one system each (`hypsN4`, `hypsKC`: the initial system on the ray along which
the `Y`-positions escape). `hypOK` runs the engine `GB.unitTest` of Section 7 on each system of the list; an answer
`true` means that the engine produced a nonzero constant as a combination of the system, so the system has no common
zero in any nontrivial commutative ring of characteristic `p` (`Lean6.Special.K4.C4.unitTest_sound`).
-/

namespace Lean6.Special.Comp.D88.Trop

open Lean6.Special.Comp

/-- The engine on every system of the list, over `ℤ/65521`, in the seventeen coordinates. -/
def hypOK (hyps : List (List (Poly Nat))) : Bool :=
  hyps.all fun s => GB.unitTest 65521 17 1000000 100000000 s

theorem n4_hyp_ok : hypOK hypsN4 = true := by native_decide

theorem kc_hyp_ok : hypOK hypsKC = true := by native_decide

end Lean6.Special.Comp.D88.Trop
