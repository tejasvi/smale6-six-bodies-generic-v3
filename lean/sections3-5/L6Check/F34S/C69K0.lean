import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C69
import L6Check.F34.Data.Common
import L6Check.F34.Data.C69
import L6Check.Certs.C5800c175b028cc82
import L6Check.Certs.Cdd820d8030a38f81

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 69, cells 0 ≤ cell < 2 of
`data/cells/c69.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 2` of class 69 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 2, core2 := 0, opn := 0 }. -/
theorem F34S_c69_k0 : checkChunkS 69 (L6.F2.diagOf 69) L6.F2.Data.cells_c69 single_69 links_69 pass_69 open43
    [("5800c175b028cc82", L6.Certs.C5800c175b028cc82), ("dd820d8030a38f81", L6.Certs.Cdd820d8030a38f81)]
    0 2 { single := 0, core1 := 2, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
