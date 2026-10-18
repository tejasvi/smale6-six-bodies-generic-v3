import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C133
import L6Check.F34.Data.Common
import L6Check.F34.Data.C133
import L6Check.Certs.C3c5862a0087ddea1
import L6Check.Certs.C4182694dbabca56f
import L6Check.Certs.C661441e082bf5fdc
import L6Check.Certs.Cd30bf77ee6877a5c
import L6Check.Certs.Cd78e7bac0db324a1
import L6Check.Certs.Ce15e707b5b269e6d

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 133, cells 0 ≤ cell < 49 of
`data/cells/c133.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 49` of class 133 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 48, core2 := 0, opn := 1 }. -/
theorem F34S_c133_k0 : checkChunkS 133 (L6.F2.diagOf 133) L6.F2.Data.cells_c133 single_133 links_133 pass_133 open43
    [("3c5862a0087ddea1", L6.Certs.C3c5862a0087ddea1), ("4182694dbabca56f", L6.Certs.C4182694dbabca56f), ("661441e082bf5fdc", L6.Certs.C661441e082bf5fdc), ("d30bf77ee6877a5c", L6.Certs.Cd30bf77ee6877a5c), ("d78e7bac0db324a1", L6.Certs.Cd78e7bac0db324a1), ("e15e707b5b269e6d", L6.Certs.Ce15e707b5b269e6d)]
    0 49 { single := 0, core1 := 48, core2 := 0, opn := 1 } = true := by
  native_decide

end L6.F34S.Checks
