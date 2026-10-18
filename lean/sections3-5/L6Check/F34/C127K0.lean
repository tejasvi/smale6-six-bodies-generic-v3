import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C127

/-! F3/F4 (Proposition 5.3), class 127, cells 0 ≤ cell < 9 of `data/cells/c127.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 9` of class 127 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 0, core2 := 0, opn := 9 }. -/
theorem F34_c127_k0 : checkChunk 127 n6 cells_127 single_127 links_127 pass_127 open43
    []
    0 9 { single := 0, core1 := 0, core2 := 0, opn := 9 } = true := by
  native_decide

end L6.F34.Checks
