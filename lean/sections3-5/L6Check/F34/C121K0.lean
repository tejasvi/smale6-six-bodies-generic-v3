import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C121
import L6Check.Certs.C71745eaf4676f6fe

/-! F3/F4 (Proposition 5.3), class 121, cells 0 ≤ cell < 1 of `data/cells/c121.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 121 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34_c121_k0 : checkChunk 121 n6 cells_121 single_121 links_121 pass_121 open43
    [("71745eaf4676f6fe", L6.Certs.C71745eaf4676f6fe)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
