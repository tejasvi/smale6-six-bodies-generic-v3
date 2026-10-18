import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C116
import L6Check.Certs.C1ca197981191c8a3
import L6Check.Certs.C2fc967393c905c4b
import L6Check.Certs.Ca046c28bb7790003

/-! F3/F4 (Proposition 5.3), class 116, cells 0 ≤ cell < 21 of `data/cells/c116.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 21` of class 116 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 6, core1 := 15, core2 := 0, opn := 0 }. -/
theorem F34_c116_k0 : checkChunk 116 n6 cells_116 single_116 links_116 pass_116 open43
    [("1ca197981191c8a3", L6.Certs.C1ca197981191c8a3), ("2fc967393c905c4b", L6.Certs.C2fc967393c905c4b), ("a046c28bb7790003", L6.Certs.Ca046c28bb7790003)]
    0 21 { single := 6, core1 := 15, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
