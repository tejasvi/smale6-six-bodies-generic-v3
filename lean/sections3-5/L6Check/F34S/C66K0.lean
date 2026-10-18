import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C66
import L6Check.F34.Data.Common
import L6Check.F34.Data.C66
import L6Check.Certs.Ccd701d6a28b8f9de

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 66, cells 0 ≤ cell < 1 of
`data/cells/c66.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 66 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34S_c66_k0 : checkChunkS 66 (L6.F2.diagOf 66) L6.F2.Data.cells_c66 single_66 links_66 pass_66 open43
    [("cd701d6a28b8f9de", L6.Certs.Ccd701d6a28b8f9de)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
