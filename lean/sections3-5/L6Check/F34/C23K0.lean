import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C23
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C2fc74d4784f04bdc
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.C4f2d64643d1b7cf8
import L6Check.Certs.C7370261e0ed5f68f
import L6Check.Certs.C7bb0ab61b0a0a34f
import L6Check.Certs.C8857db9784f0fc0c
import L6Check.Certs.C8e67dabaee43118e
import L6Check.Certs.Cbc43a551b6dae1dc
import L6Check.Certs.Cc141c278d23fd57b
import L6Check.Certs.Ccf7f7ca69feb518d
import L6Check.Certs.Ce14a1acf0eb39ff8

/-! F3/F4 (Proposition 5.3), class 23, cells 0 ≤ cell < 239 of `data/cells/c23.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 239` of class 23 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 102, core1 := 137, core2 := 0, opn := 0 }. -/
theorem F34_c23_k0 : checkChunk 23 n6 cells_23 single_23 links_23 pass_23 open43
    [("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("2fc74d4784f04bdc", L6.Certs.C2fc74d4784f04bdc), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("4f2d64643d1b7cf8", L6.Certs.C4f2d64643d1b7cf8), ("7370261e0ed5f68f", L6.Certs.C7370261e0ed5f68f), ("7bb0ab61b0a0a34f", L6.Certs.C7bb0ab61b0a0a34f), ("8857db9784f0fc0c", L6.Certs.C8857db9784f0fc0c), ("8e67dabaee43118e", L6.Certs.C8e67dabaee43118e), ("bc43a551b6dae1dc", L6.Certs.Cbc43a551b6dae1dc), ("c141c278d23fd57b", L6.Certs.Cc141c278d23fd57b), ("cf7f7ca69feb518d", L6.Certs.Ccf7f7ca69feb518d), ("e14a1acf0eb39ff8", L6.Certs.Ce14a1acf0eb39ff8)]
    0 239 { single := 102, core1 := 137, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
