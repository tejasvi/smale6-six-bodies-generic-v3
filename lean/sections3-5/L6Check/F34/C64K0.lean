import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C64
import L6Check.Certs.C58aef968e8ec9dde
import L6Check.Certs.C9c88b57518e5a34d
import L6Check.Certs.Cdd820d8030a38f81
import L6Check.Certs.Cf61c618785573ea5

/-! F3/F4 (Proposition 5.3), class 64, cells 0 ≤ cell < 162 of `data/cells/c64.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 162` of class 64 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 64, core1 := 98, core2 := 0, opn := 0 }. -/
theorem F34_c64_k0 : checkChunk 64 n6 cells_64 single_64 links_64 pass_64 open43
    [("58aef968e8ec9dde", L6.Certs.C58aef968e8ec9dde), ("9c88b57518e5a34d", L6.Certs.C9c88b57518e5a34d), ("dd820d8030a38f81", L6.Certs.Cdd820d8030a38f81), ("f61c618785573ea5", L6.Certs.Cf61c618785573ea5)]
    0 162 { single := 64, core1 := 98, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
