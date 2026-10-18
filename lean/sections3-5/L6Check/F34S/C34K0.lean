import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C34
import L6Check.F34.Data.Common
import L6Check.F34.Data.C34
import L6Check.Certs.Ca43053ecd5a89707

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 34, cells 0 ≤ cell < 1 of
`data/cells/c34.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 34 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34S_c34_k0 : checkChunkS 34 (L6.F2.diagOf 34) L6.F2.Data.cells_c34 single_34 links_34 pass_34 open43
    [("a43053ecd5a89707", L6.Certs.Ca43053ecd5a89707)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
