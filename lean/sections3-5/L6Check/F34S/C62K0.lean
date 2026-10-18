import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C62
import L6Check.F34.Data.Common
import L6Check.F34.Data.C62
import L6Check.Certs.C70f76847badad122

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 62, cells 0 ≤ cell < 14 of
`data/cells/c62.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 14` of class 62 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 14, core2 := 0, opn := 0 }. -/
theorem F34S_c62_k0 : checkChunkS 62 (L6.F2.diagOf 62) L6.F2.Data.cells_c62 single_62 links_62 pass_62 open43
    [("70f76847badad122", L6.Certs.C70f76847badad122)]
    0 14 { single := 0, core1 := 14, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
