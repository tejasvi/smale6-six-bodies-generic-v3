import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C123
import L6Check.F34.Data.Common
import L6Check.F34.Data.C123
import L6Check.Certs.Cbb7465e3ffc512e5

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 123, cells 0 ≤ cell < 1 of
`data/cells/c123.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 123 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34S_c123_k0 : checkChunkS 123 (L6.F2.diagOf 123) L6.F2.Data.cells_c123 single_123 links_123 pass_123 open43
    [("bb7465e3ffc512e5", L6.Certs.Cbb7465e3ffc512e5)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
