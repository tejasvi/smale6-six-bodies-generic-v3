import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C57
import L6Check.Certs.C9853f5adfb8f7e7c

/-! F3/F4 (Proposition 5.3), class 57, cells 0 ≤ cell < 2 of `data/cells/c57.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 2` of class 57 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 2, core2 := 0, opn := 0 }. -/
theorem F34_c57_k0 : checkChunk 57 n6 cells_57 single_57 links_57 pass_57 open43
    [("9853f5adfb8f7e7c", L6.Certs.C9853f5adfb8f7e7c)]
    0 2 { single := 0, core1 := 2, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
