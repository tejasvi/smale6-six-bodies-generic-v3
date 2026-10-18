import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C24
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.Cc141c278d23fd57b

/-! F3/F4 (Proposition 5.3), class 24, cells 0 ≤ cell < 72 of `data/cells/c24.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 72` of class 24 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 24, core1 := 48, core2 := 0, opn := 0 }. -/
theorem F34_c24_k0 : checkChunk 24 n6 cells_24 single_24 links_24 pass_24 open43
    [("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("c141c278d23fd57b", L6.Certs.Cc141c278d23fd57b)]
    0 72 { single := 24, core1 := 48, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
