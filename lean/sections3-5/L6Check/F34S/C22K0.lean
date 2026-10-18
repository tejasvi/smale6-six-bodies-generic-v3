import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C22
import L6Check.F34.Data.Common
import L6Check.F34.Data.C22
import L6Check.Certs.Cbc43a551b6dae1dc

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 22, cells 0 ≤ cell < 2 of
`data/cells/c22.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 2` of class 22 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 2, core2 := 0, opn := 0 }. -/
theorem F34S_c22_k0 : checkChunkS 22 (L6.F2.diagOf 22) L6.F2.Data.cells_c22 single_22 links_22 pass_22 open43
    [("bc43a551b6dae1dc", L6.Certs.Cbc43a551b6dae1dc)]
    0 2 { single := 0, core1 := 2, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
