import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C53
import L6Check.F34.Data.Common
import L6Check.F34.Data.C53
import L6Check.Certs.C8ee387c2184c925d

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 53, cells 0 ≤ cell < 3 of
`data/cells/c53.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 3` of class 53 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 2, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34S_c53_k0 : checkChunkS 53 (L6.F2.diagOf 53) L6.F2.Data.cells_c53 single_53 links_53 pass_53 open43
    [("8ee387c2184c925d", L6.Certs.C8ee387c2184c925d)]
    0 3 { single := 2, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
