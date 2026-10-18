import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C16
import L6Check.Certs.C39337c5b1728651c
import L6Check.Certs.C689770ee9044da22
import L6Check.Certs.C82e1dc0d540f7949
import L6Check.Certs.Cadb61a2079b24867
import L6Check.Certs.Cb76600618d698a5e

/-! F3/F4 (Proposition 5.3), class 16, cells 0 ≤ cell < 28 of `data/cells/c16.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 28` of class 16 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 28, core2 := 0, opn := 0 }. -/
theorem F34_c16_k0 : checkChunk 16 n6 cells_16 single_16 links_16 pass_16 open43
    [("39337c5b1728651c", L6.Certs.C39337c5b1728651c), ("689770ee9044da22", L6.Certs.C689770ee9044da22), ("82e1dc0d540f7949", L6.Certs.C82e1dc0d540f7949), ("adb61a2079b24867", L6.Certs.Cadb61a2079b24867), ("b76600618d698a5e", L6.Certs.Cb76600618d698a5e)]
    0 28 { single := 0, core1 := 28, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
