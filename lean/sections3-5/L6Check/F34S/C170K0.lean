import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C170
import L6Check.F34.Data.Common
import L6Check.F34.Data.C170
import L6Check.Certs.Cc7f832c444000333

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 170, cells 0 ≤ cell < 9 of
`data/cells/c170.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 9` of class 170 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 9, core2 := 0, opn := 0 }. -/
theorem F34S_c170_k0 : checkChunkS 170 (L6.F2.diagOf 170) L6.F2.Data.cells_c170 single_170 links_170 pass_170 open43
    [("c7f832c444000333", L6.Certs.Cc7f832c444000333)]
    0 9 { single := 0, core1 := 9, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
