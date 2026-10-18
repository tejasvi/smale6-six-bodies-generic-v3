import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C120
import L6Check.F34.Data.Common
import L6Check.F34.Data.C120
import L6Check.Certs.Cf0cd9a6da7e7cac4

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 120, cells 0 ≤ cell < 2 of
`data/cells/c120.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 2` of class 120 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 2, core2 := 0, opn := 0 }. -/
theorem F34S_c120_k0 : checkChunkS 120 (L6.F2.diagOf 120) L6.F2.Data.cells_c120 single_120 links_120 pass_120 open43
    [("f0cd9a6da7e7cac4", L6.Certs.Cf0cd9a6da7e7cac4)]
    0 2 { single := 0, core1 := 2, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
