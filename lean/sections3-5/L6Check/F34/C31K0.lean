import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C31
import L6Check.Certs.C3d714201c8be7b7f
import L6Check.Certs.C5bcf860e57095e47
import L6Check.Certs.Cb7d19dd1e1382c3f
import L6Check.Certs.Cd09943b8475b721e
import L6Check.Certs.Cdc7356ab11f9443f
import L6Check.Certs.Cf819a94c7e21aa42

/-! F3/F4 (Proposition 5.3), class 31, cells 0 ≤ cell < 49 of `data/cells/c31.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 49` of class 31 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 48, core2 := 0, opn := 1 }. -/
theorem F34_c31_k0 : checkChunk 31 n6 cells_31 single_31 links_31 pass_31 open43
    [("3d714201c8be7b7f", L6.Certs.C3d714201c8be7b7f), ("5bcf860e57095e47", L6.Certs.C5bcf860e57095e47), ("b7d19dd1e1382c3f", L6.Certs.Cb7d19dd1e1382c3f), ("d09943b8475b721e", L6.Certs.Cd09943b8475b721e), ("dc7356ab11f9443f", L6.Certs.Cdc7356ab11f9443f), ("f819a94c7e21aa42", L6.Certs.Cf819a94c7e21aa42)]
    0 49 { single := 0, core1 := 48, core2 := 0, opn := 1 } = true := by
  native_decide

end L6.F34.Checks
