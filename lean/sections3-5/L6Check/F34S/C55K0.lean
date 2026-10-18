import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C55
import L6Check.F34.Data.Common
import L6Check.F34.Data.C55

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 55, cells 0 ≤ cell < 24 of
`data/cells/c55.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 24` of class 55 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 24, core1 := 0, core2 := 0, opn := 0 }. -/
theorem F34S_c55_k0 : checkChunkS 55 (L6.F2.diagOf 55) L6.F2.Data.cells_c55 single_55 links_55 pass_55 open43
    []
    0 24 { single := 24, core1 := 0, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
