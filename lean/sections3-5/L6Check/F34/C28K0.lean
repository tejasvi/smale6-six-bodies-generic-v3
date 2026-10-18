import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C28
import L6Check.Certs.C5b12e430152f9e3c

/-! F3/F4 (Proposition 5.3), class 28, cells 0 ≤ cell < 3 of `data/cells/c28.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 3` of class 28 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 2, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34_c28_k0 : checkChunk 28 n6 cells_28 single_28 links_28 pass_28 open43
    [("5b12e430152f9e3c", L6.Certs.C5b12e430152f9e3c)]
    0 3 { single := 2, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
