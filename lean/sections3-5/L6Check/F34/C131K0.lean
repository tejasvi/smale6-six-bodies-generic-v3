import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C131

/-! F3/F4 (Proposition 5.3), class 131, cells 0 ≤ cell < 196 of `data/cells/c131.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 196` of class 131 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 196, core1 := 0, core2 := 0, opn := 0 }. -/
theorem F34_c131_k0 : checkChunk 131 n6 cells_131 single_131 links_131 pass_131 open43
    []
    0 196 { single := 196, core1 := 0, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
