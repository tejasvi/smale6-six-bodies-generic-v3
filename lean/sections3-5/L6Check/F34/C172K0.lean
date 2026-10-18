import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C172
import L6Check.Certs.C2b4c18bd70ef0eb0

/-! F3/F4 (Proposition 5.3), class 172, cells 0 ≤ cell < 6 of `data/cells/c172.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 6` of class 172 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 6, core2 := 0, opn := 0 }. -/
theorem F34_c172_k0 : checkChunk 172 n6 cells_172 single_172 links_172 pass_172 open43
    [("2b4c18bd70ef0eb0", L6.Certs.C2b4c18bd70ef0eb0)]
    0 6 { single := 0, core1 := 6, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
