import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C24
import L6Check.F34.Data.Common
import L6Check.F34.Data.C24
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.Cc141c278d23fd57b

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 24, cells 0 ≤ cell < 72 of
`data/cells/c24.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 72` of class 24 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 24, core1 := 48, core2 := 0, opn := 0 }. -/
theorem F34S_c24_k0 : checkChunkS 24 (L6.F2.diagOf 24) L6.F2.Data.cells_c24 single_24 links_24 pass_24 open43
    [("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("c141c278d23fd57b", L6.Certs.Cc141c278d23fd57b)]
    0 72 { single := 24, core1 := 48, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
