import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C171
import L6Check.Certs.C26b4de05195d96d7
import L6Check.Certs.C2b4c18bd70ef0eb0
import L6Check.Certs.C91deedccc2b780ca
import L6Check.Certs.Cc412e555eaa24389

/-! F3/F4 (Proposition 5.3), class 171, cells 0 ≤ cell < 19 of `data/cells/c171.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 19` of class 171 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 19, core2 := 0, opn := 0 }. -/
theorem F34_c171_k0 : checkChunk 171 n6 cells_171 single_171 links_171 pass_171 open43
    [("26b4de05195d96d7", L6.Certs.C26b4de05195d96d7), ("2b4c18bd70ef0eb0", L6.Certs.C2b4c18bd70ef0eb0), ("91deedccc2b780ca", L6.Certs.C91deedccc2b780ca), ("c412e555eaa24389", L6.Certs.Cc412e555eaa24389)]
    0 19 { single := 0, core1 := 19, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
