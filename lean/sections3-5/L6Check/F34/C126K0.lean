import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C126
import L6Check.Certs.C2069cc24c5c894a6
import L6Check.Certs.C780a1fce40bcc09a

/-! F3/F4 (Proposition 5.3), class 126, cells 0 ≤ cell < 27 of `data/cells/c126.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 27` of class 126 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 27, core2 := 0, opn := 0 }. -/
theorem F34_c126_k0 : checkChunk 126 n6 cells_126 single_126 links_126 pass_126 open43
    [("2069cc24c5c894a6", L6.Certs.C2069cc24c5c894a6), ("780a1fce40bcc09a", L6.Certs.C780a1fce40bcc09a)]
    0 27 { single := 0, core1 := 27, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
