import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C172
import L6Check.F34.Data.Common
import L6Check.F34.Data.C172
import L6Check.Certs.C2b4c18bd70ef0eb0

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 172, cells 0 ≤ cell < 6 of
`data/cells/c172.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 6` of class 172 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 6, core2 := 0, opn := 0 }. -/
theorem F34S_c172_k0 : checkChunkS 172 (L6.F2.diagOf 172) L6.F2.Data.cells_c172 single_172 links_172 pass_172 open43
    [("2b4c18bd70ef0eb0", L6.Certs.C2b4c18bd70ef0eb0)]
    0 6 { single := 0, core1 := 6, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
