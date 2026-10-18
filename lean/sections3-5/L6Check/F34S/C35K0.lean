import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C35
import L6Check.F34.Data.Common
import L6Check.F34.Data.C35
import L6Check.Certs.C6671537c18c25ec5

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 35, cells 0 ≤ cell < 1 of
`data/cells/c35.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1` of class 35 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 1, core2 := 0, opn := 0 }. -/
theorem F34S_c35_k0 : checkChunkS 35 (L6.F2.diagOf 35) L6.F2.Data.cells_c35 single_35 links_35 pass_35 open43
    [("6671537c18c25ec5", L6.Certs.C6671537c18c25ec5)]
    0 1 { single := 0, core1 := 1, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
