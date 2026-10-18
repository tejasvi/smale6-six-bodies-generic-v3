import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C10
import L6Check.F34.Data.Common
import L6Check.F34.Data.C10
import L6Check.Certs.C2d23d5b4967e966f
import L6Check.Certs.C9b9bbf8a21ffc7e0

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 10, cells 0 ≤ cell < 10 of
`data/cells/c10.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 10` of class 10 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 10, core2 := 0, opn := 0 }. -/
theorem F34S_c10_k0 : checkChunkS 10 (L6.F2.diagOf 10) L6.F2.Data.cells_c10 single_10 links_10 pass_10 open43
    [("2d23d5b4967e966f", L6.Certs.C2d23d5b4967e966f), ("9b9bbf8a21ffc7e0", L6.Certs.C9b9bbf8a21ffc7e0)]
    0 10 { single := 0, core1 := 10, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
