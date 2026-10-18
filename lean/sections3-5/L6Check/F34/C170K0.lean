import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C170
import L6Check.Certs.Cc7f832c444000333

/-! F3/F4 (Proposition 5.3), class 170, cells 0 ≤ cell < 9 of `data/cells/c170.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 9` of class 170 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 9, core2 := 0, opn := 0 }. -/
theorem F34_c170_k0 : checkChunk 170 n6 cells_170 single_170 links_170 pass_170 open43
    [("c7f832c444000333", L6.Certs.Cc7f832c444000333)]
    0 9 { single := 0, core1 := 9, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
