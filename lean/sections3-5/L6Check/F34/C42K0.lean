import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C42
import L6Check.Certs.C495be6eb51908b56
import L6Check.Certs.C553a98a51c8385e5

/-! F3/F4 (Proposition 5.3), class 42, cells 0 ≤ cell < 20 of `data/cells/c42.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 20` of class 42 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 20, core2 := 0, opn := 0 }. -/
theorem F34_c42_k0 : checkChunk 42 n6 cells_42 single_42 links_42 pass_42 open43
    [("495be6eb51908b56", L6.Certs.C495be6eb51908b56), ("553a98a51c8385e5", L6.Certs.C553a98a51c8385e5)]
    0 20 { single := 0, core1 := 20, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
