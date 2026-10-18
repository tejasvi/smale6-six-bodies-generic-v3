import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C20
import L6Check.Certs.C2ee4f4eb2ce5ee53
import L6Check.Certs.C2fc967393c905c4b
import L6Check.Certs.C5bfc873484475034

/-! F3/F4 (Proposition 5.3), class 20, cells 0 ≤ cell < 13 of `data/cells/c20.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 13` of class 20 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 13, core2 := 0, opn := 0 }. -/
theorem F34_c20_k0 : checkChunk 20 n6 cells_20 single_20 links_20 pass_20 open43
    [("2ee4f4eb2ce5ee53", L6.Certs.C2ee4f4eb2ce5ee53), ("2fc967393c905c4b", L6.Certs.C2fc967393c905c4b), ("5bfc873484475034", L6.Certs.C5bfc873484475034)]
    0 13 { single := 0, core1 := 13, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
