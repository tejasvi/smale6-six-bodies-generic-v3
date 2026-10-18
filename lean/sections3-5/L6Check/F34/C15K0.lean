import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C15
import L6Check.Certs.C22b9fc38c827b912
import L6Check.Certs.C54483d807bd4f917
import L6Check.Certs.C61a5deba861f1dfd
import L6Check.Certs.C7f8d702f69d126f9
import L6Check.Certs.Cd83618e5b93bab5a

/-! F3/F4 (Proposition 5.3), class 15, cells 0 ≤ cell < 42 of `data/cells/c15.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 42` of class 15 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 29, core1 := 13, core2 := 0, opn := 0 }. -/
theorem F34_c15_k0 : checkChunk 15 n6 cells_15 single_15 links_15 pass_15 open43
    [("22b9fc38c827b912", L6.Certs.C22b9fc38c827b912), ("54483d807bd4f917", L6.Certs.C54483d807bd4f917), ("61a5deba861f1dfd", L6.Certs.C61a5deba861f1dfd), ("7f8d702f69d126f9", L6.Certs.C7f8d702f69d126f9), ("d83618e5b93bab5a", L6.Certs.Cd83618e5b93bab5a)]
    0 42 { single := 29, core1 := 13, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
