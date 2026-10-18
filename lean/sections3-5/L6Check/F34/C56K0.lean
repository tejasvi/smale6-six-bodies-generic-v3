import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C56
import L6Check.Certs.C0fd6de36cae427b6
import L6Check.Certs.C3b346da30054d354
import L6Check.Certs.C495be6eb51908b56
import L6Check.Certs.C5bd3aa4c434c4cd6
import L6Check.Certs.C8857db9784f0fc0c
import L6Check.Certs.Ca3f35edf8c8e8930

/-! F3/F4 (Proposition 5.3), class 56, cells 0 ≤ cell < 37 of `data/cells/c56.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 37` of class 56 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 6, core1 := 31, core2 := 0, opn := 0 }. -/
theorem F34_c56_k0 : checkChunk 56 n6 cells_56 single_56 links_56 pass_56 open43
    [("0fd6de36cae427b6", L6.Certs.C0fd6de36cae427b6), ("3b346da30054d354", L6.Certs.C3b346da30054d354), ("495be6eb51908b56", L6.Certs.C495be6eb51908b56), ("5bd3aa4c434c4cd6", L6.Certs.C5bd3aa4c434c4cd6), ("8857db9784f0fc0c", L6.Certs.C8857db9784f0fc0c), ("a3f35edf8c8e8930", L6.Certs.Ca3f35edf8c8e8930)]
    0 37 { single := 6, core1 := 31, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
