import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C34
import L6Check.Certs.Ca43053ecd5a89707

/-! F3/F4 (Proposition 5.3), class 34, cells 0 ≤ cell < 1 of `data/cells/c34.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 34 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34_c34_k0 : checkChunk 34 n6 cells_34 single_34 links_34 pass_34 open43
    [("a43053ecd5a89707", L6.Certs.Ca43053ecd5a89707)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
