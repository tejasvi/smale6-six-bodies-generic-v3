import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C67
import L6Check.Certs.C5800c175b028cc82
import L6Check.Certs.Cdd820d8030a38f81

/-! F3/F4 (Proposition 5.3), class 67, cells 0 ≤ cell < 2 of `data/cells/c67.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 2` of class 67 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 2, core2 := 0, opn := 0 }. -/
theorem F34_c67_k0 : checkChunk 67 n6 cells_67 single_67 links_67 pass_67 open43
    [("5800c175b028cc82", L6.Certs.C5800c175b028cc82), ("dd820d8030a38f81", L6.Certs.Cdd820d8030a38f81)]
    0 2 { single := 0, core1 := 2, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
