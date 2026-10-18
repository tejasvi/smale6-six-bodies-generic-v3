import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C147
import L6Check.F34.Data.Common
import L6Check.F34.Data.C147
import L6Check.Certs.C1552f9aba0578e3f
import L6Check.Certs.C8c688c0db558268f
import L6Check.Certs.Cccbf1c95d4bb3b2f

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 147, cells 0 ≤ cell < 63 of
`data/cells/c147.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 63` of class 147 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 54, core2 := 0, opn := 9 }. -/
theorem F34S_c147_k0 : checkChunkS 147 (L6.F2.diagOf 147) L6.F2.Data.cells_c147 single_147 links_147 pass_147 open43
    [("1552f9aba0578e3f", L6.Certs.C1552f9aba0578e3f), ("8c688c0db558268f", L6.Certs.C8c688c0db558268f), ("ccbf1c95d4bb3b2f", L6.Certs.Cccbf1c95d4bb3b2f)]
    0 63 { single := 0, core1 := 54, core2 := 0, opn := 9 } = true := by
  native_decide

end L6.F34S.Checks
