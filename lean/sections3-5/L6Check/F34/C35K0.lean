import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C35
import L6Check.Certs.C6671537c18c25ec5

/-! F3/F4 (Proposition 5.3), class 35, cells 0 ≤ cell < 1 of `data/cells/c35.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 35 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34_c35_k0 : checkChunk 35 n6 cells_35 single_35 links_35 pass_35 open43
    [("6671537c18c25ec5", L6.Certs.C6671537c18c25ec5)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
