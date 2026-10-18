import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C84
import L6Check.Certs.C9ff5f6dec2baab1d

/-! F3/F4 (Proposition 5.3), class 84, cells 0 ≤ cell < 1 of `data/cells/c84.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 84 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34_c84_k0 : checkChunk 84 n6 cells_84 single_84 links_84 pass_84 open43
    [("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
