import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C55

/-! F3/F4 (Proposition 5.3), class 55, cells 0 ≤ cell < 24 of `data/cells/c55.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 24` of class 55 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 24, core1 := 0, core2 := 0, opn := 0 }. -/
theorem F34_c55_k0 : checkChunk 55 n6 cells_55 single_55 links_55 pass_55 open43
    []
    0 24 { single := 24, core1 := 0, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
