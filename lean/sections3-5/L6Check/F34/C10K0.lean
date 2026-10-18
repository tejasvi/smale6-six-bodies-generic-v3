import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C10
import L6Check.Certs.C2d23d5b4967e966f
import L6Check.Certs.C9b9bbf8a21ffc7e0

/-! F3/F4 (Proposition 5.3), class 10, cells 0 ≤ cell < 10 of `data/cells/c10.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 10` of class 10 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 10, core2 := 0, opn := 0 }. -/
theorem F34_c10_k0 : checkChunk 10 n6 cells_10 single_10 links_10 pass_10 open43
    [("2d23d5b4967e966f", L6.Certs.C2d23d5b4967e966f), ("9b9bbf8a21ffc7e0", L6.Certs.C9b9bbf8a21ffc7e0)]
    0 10 { single := 0, core1 := 10, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
