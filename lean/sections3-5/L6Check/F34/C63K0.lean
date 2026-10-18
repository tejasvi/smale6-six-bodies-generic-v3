import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C63
import L6Check.Certs.C70f76847badad122

/-! F3/F4 (Proposition 5.3), class 63, cells 0 ≤ cell < 7 of `data/cells/c63.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 7` of class 63 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 7, core2 := 0, opn := 0 }. -/
theorem F34_c63_k0 : checkChunk 63 n6 cells_63 single_63 links_63 pass_63 open43
    [("70f76847badad122", L6.Certs.C70f76847badad122)]
    0 7 { single := 0, core1 := 7, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
