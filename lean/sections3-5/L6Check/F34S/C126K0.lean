import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C126
import L6Check.F34.Data.Common
import L6Check.F34.Data.C126
import L6Check.Certs.C2069cc24c5c894a6
import L6Check.Certs.C780a1fce40bcc09a

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 126, cells 0 ≤ cell < 27 of
`data/cells/c126.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 27` of class 126 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 27, core2 := 0, opn := 0 }. -/
theorem F34S_c126_k0 : checkChunkS 126 (L6.F2.diagOf 126) L6.F2.Data.cells_c126 single_126 links_126 pass_126 open43
    [("2069cc24c5c894a6", L6.Certs.C2069cc24c5c894a6), ("780a1fce40bcc09a", L6.Certs.C780a1fce40bcc09a)]
    0 27 { single := 0, core1 := 27, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
