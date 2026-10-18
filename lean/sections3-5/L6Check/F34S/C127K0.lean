import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C127
import L6Check.F34.Data.Common
import L6Check.F34.Data.C127

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 127, cells 0 ≤ cell < 9 of
`data/cells/c127.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 9` of class 127 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 0, core2 := 0, opn := 9 }. -/
theorem F34S_c127_k0 : checkChunkS 127 (L6.F2.diagOf 127) L6.F2.Data.cells_c127 single_127 links_127 pass_127 open43
    []
    0 9 { single := 0, core1 := 0, core2 := 0, opn := 9 } = true := by
  native_decide

end L6.F34S.Checks
