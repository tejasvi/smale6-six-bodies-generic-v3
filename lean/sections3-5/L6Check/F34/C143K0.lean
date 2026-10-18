import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C143
import L6Check.Certs.C1552f9aba0578e3f
import L6Check.Certs.C8c688c0db558268f
import L6Check.Certs.Cccbf1c95d4bb3b2f

/-! F3/F4 (Proposition 5.3), class 143, cells 0 ≤ cell < 77 of `data/cells/c143.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 77` of class 143 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 66, core2 := 0, opn := 11 }. -/
theorem F34_c143_k0 : checkChunk 143 n6 cells_143 single_143 links_143 pass_143 open43
    [("1552f9aba0578e3f", L6.Certs.C1552f9aba0578e3f), ("8c688c0db558268f", L6.Certs.C8c688c0db558268f), ("ccbf1c95d4bb3b2f", L6.Certs.Cccbf1c95d4bb3b2f)]
    0 77 { single := 0, core1 := 66, core2 := 0, opn := 11 } = true := by
  native_decide

end L6.F34.Checks
