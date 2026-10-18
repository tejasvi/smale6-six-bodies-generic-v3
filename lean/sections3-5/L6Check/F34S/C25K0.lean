import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C25
import L6Check.F34.Data.Common
import L6Check.F34.Data.C25
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C19998d415ed1923d
import L6Check.Certs.C26ab6a31ef0dc88a
import L6Check.Certs.C2fc74d4784f04bdc
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.C4f2d64643d1b7cf8
import L6Check.Certs.C6854bcb779f23df6
import L6Check.Certs.C7bb0ab61b0a0a34f
import L6Check.Certs.Cbbfdf82e3e6adfc3
import L6Check.Certs.Cc141c278d23fd57b
import L6Check.Certs.Ccf7f7ca69feb518d
import L6Check.Certs.Ce14a1acf0eb39ff8
import L6Check.Certs.Ce2448096808df218

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 25, cells 0 ≤ cell < 88 of
`data/cells/c25.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 88` of class 25 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 18, core1 := 70, core2 := 0, opn := 0 }. -/
theorem F34S_c25_k0 : checkChunkS 25 (L6.F2.diagOf 25) L6.F2.Data.cells_c25 single_25 links_25 pass_25 open43
    [("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("19998d415ed1923d", L6.Certs.C19998d415ed1923d), ("26ab6a31ef0dc88a", L6.Certs.C26ab6a31ef0dc88a), ("2fc74d4784f04bdc", L6.Certs.C2fc74d4784f04bdc), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("4f2d64643d1b7cf8", L6.Certs.C4f2d64643d1b7cf8), ("6854bcb779f23df6", L6.Certs.C6854bcb779f23df6), ("7bb0ab61b0a0a34f", L6.Certs.C7bb0ab61b0a0a34f), ("bbfdf82e3e6adfc3", L6.Certs.Cbbfdf82e3e6adfc3), ("c141c278d23fd57b", L6.Certs.Cc141c278d23fd57b), ("cf7f7ca69feb518d", L6.Certs.Ccf7f7ca69feb518d), ("e14a1acf0eb39ff8", L6.Certs.Ce14a1acf0eb39ff8), ("e2448096808df218", L6.Certs.Ce2448096808df218)]
    0 88 { single := 18, core1 := 70, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
