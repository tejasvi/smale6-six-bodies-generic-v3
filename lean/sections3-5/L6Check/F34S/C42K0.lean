import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C42
import L6Check.F34.Data.Common
import L6Check.F34.Data.C42
import L6Check.Certs.C495be6eb51908b56
import L6Check.Certs.C553a98a51c8385e5

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 42, cells 0 ≤ cell < 20 of
`data/cells/c42.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 20` of class 42 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 20, core2 := 0, opn := 0 }. -/
theorem F34S_c42_k0 : checkChunkS 42 (L6.F2.diagOf 42) L6.F2.Data.cells_c42 single_42 links_42 pass_42 open43
    [("495be6eb51908b56", L6.Certs.C495be6eb51908b56), ("553a98a51c8385e5", L6.Certs.C553a98a51c8385e5)]
    0 20 { single := 0, core1 := 20, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
