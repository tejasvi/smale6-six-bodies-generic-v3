import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C169
import L6Check.F34.Data.Common
import L6Check.F34.Data.C169
import L6Check.Certs.Cc7f832c444000333

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 169, cells 0 ≤ cell < 18 of
`data/cells/c169.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 18` of class 169 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 18, core2 := 0, opn := 0 }. -/
theorem F34S_c169_k0 : checkChunkS 169 (L6.F2.diagOf 169) L6.F2.Data.cells_c169 single_169 links_169 pass_169 open43
    [("c7f832c444000333", L6.Certs.Cc7f832c444000333)]
    0 18 { single := 0, core1 := 18, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
