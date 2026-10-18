import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C117
import L6Check.Certs.C6d21e7eccd073b25
import L6Check.Certs.C71745eaf4676f6fe

/-! F3/F4 (Proposition 5.3), class 117, cells 0 ≤ cell < 2 of `data/cells/c117.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 2` of class 117 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 2, core2 := 0, opn := 0 }. -/
theorem F34_c117_k0 : checkChunk 117 n6 cells_117 single_117 links_117 pass_117 open43
    [("6d21e7eccd073b25", L6.Certs.C6d21e7eccd073b25), ("71745eaf4676f6fe", L6.Certs.C71745eaf4676f6fe)]
    0 2 { single := 0, core1 := 2, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
