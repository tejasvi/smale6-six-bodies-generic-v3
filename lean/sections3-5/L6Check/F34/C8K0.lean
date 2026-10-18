import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C8
import L6Check.Certs.C3c9db6d4a33383e9

/-! F3/F4 (Proposition 5.3), class 8, cells 0 ≤ cell < 1 of `data/cells/c8.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 8 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34_c8_k0 : checkChunk 8 n6 cells_8 single_8 links_8 pass_8 open43
    [("3c9db6d4a33383e9", L6.Certs.C3c9db6d4a33383e9)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
