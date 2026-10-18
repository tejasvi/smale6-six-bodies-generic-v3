import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C146
import L6Check.Certs.C2e4383462f92db6b
import L6Check.Certs.C51ee843597cff9f3
import L6Check.Certs.Cb572ba022f4eb792
import L6Check.Certs.Cc7f832c444000333

/-! F3/F4 (Proposition 5.3), class 146, cells 0 ≤ cell < 81 of `data/cells/c146.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 81` of class 146 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 81, core2 := 0, opn := 0 }. -/
theorem F34_c146_k0 : checkChunk 146 n6 cells_146 single_146 links_146 pass_146 open43
    [("2e4383462f92db6b", L6.Certs.C2e4383462f92db6b), ("51ee843597cff9f3", L6.Certs.C51ee843597cff9f3), ("b572ba022f4eb792", L6.Certs.Cb572ba022f4eb792), ("c7f832c444000333", L6.Certs.Cc7f832c444000333)]
    0 81 { single := 0, core1 := 81, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
