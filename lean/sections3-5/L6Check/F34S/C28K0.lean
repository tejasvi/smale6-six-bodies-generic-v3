import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C28
import L6Check.F34.Data.Common
import L6Check.F34.Data.C28
import L6Check.Certs.C5b12e430152f9e3c

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 28, cells 0 ≤ cell < 3 of
`data/cells/c28.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 3` of class 28 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 2, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34S_c28_k0 : checkChunkS 28 (L6.F2.diagOf 28) L6.F2.Data.cells_c28 single_28 links_28 pass_28 open43
    [("5b12e430152f9e3c", L6.Certs.C5b12e430152f9e3c)]
    0 3 { single := 2, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
