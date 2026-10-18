import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C57
import L6Check.F34.Data.Common
import L6Check.F34.Data.C57
import L6Check.Certs.C9853f5adfb8f7e7c

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 57, cells 0 ≤ cell < 2 of
`data/cells/c57.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 2` of class 57 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 2, core2 := 0, opn := 0 }. -/
theorem F34S_c57_k0 : checkChunkS 57 (L6.F2.diagOf 57) L6.F2.Data.cells_c57 single_57 links_57 pass_57 open43
    [("9853f5adfb8f7e7c", L6.Certs.C9853f5adfb8f7e7c)]
    0 2 { single := 0, core1 := 2, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
