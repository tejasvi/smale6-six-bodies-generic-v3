import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C8
import L6Check.F34.Data.Common
import L6Check.F34.Data.C8
import L6Check.Certs.C3c9db6d4a33383e9

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 8, cells 0 ≤ cell < 1 of
`data/cells/c8.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 8 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34S_c8_k0 : checkChunkS 8 (L6.F2.diagOf 8) L6.F2.Data.cells_c8 single_8 links_8 pass_8 open43
    [("3c9db6d4a33383e9", L6.Certs.C3c9db6d4a33383e9)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
