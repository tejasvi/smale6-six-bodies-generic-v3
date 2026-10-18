import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C173
import L6Check.F34.Data.Common
import L6Check.F34.Data.C173
import L6Check.Certs.C26b4de05195d96d7

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 173, cells 0 ≤ cell < 1 of
`data/cells/c173.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 173 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34S_c173_k0 : checkChunkS 173 (L6.F2.diagOf 173) L6.F2.Data.cells_c173 single_173 links_173 pass_173 open43
    [("26b4de05195d96d7", L6.Certs.C26b4de05195d96d7)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
