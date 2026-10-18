import CC6Full.Interface
import CC6Compose.Heavy
import CC6Compose.E4
import CC6Compose.C4
import CC6Compose.Boxes
import CC6Compose.Integrality

/-!
# The computations of Sections 6 and 7 that are connected, and what remains

`sevenCerts'_of` proves `SevenCerts'` (the hypothesis of `seven_excluded'`) from the two statements that the
certificate project does not provide yet: the dimension bounds of Lemma 6.19(b) (`D88Dim`, `D94Dim`). The other eight
components are the bridges `heavyFact`, `heavyFact3`, `e4NoZero`, `c4Cert`, `d88Box`, `d94Box`, and `d88Int`,
`d94Int` (Lemma 6.18 by `goodred_torus_opt` from the tropical certificates of Lemma 6.19(a)).
-/

namespace CC6Compose

open CC6Full CC6Full.Six

theorem sevenCerts'_of (h88d : D88Dim) (h94d : D94Dim) : SevenCerts' :=
  ⟨heavyFact, heavyFact3, e4NoZero, c4Cert, d88Int, h88d, d88Box, d94Int, h94d, d94Box⟩

end CC6Compose
