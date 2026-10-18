import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C167
import L6Check.Certs.C2e4383462f92db6b
import L6Check.Certs.C392aea6662b7eaef
import L6Check.Certs.Cb1a8296b2bd2b206
import L6Check.Certs.Cb8869a68e220593f

/-! F3/F4 (Proposition 5.3), class 167, cells 0 ≤ cell < 72 of `data/cells/c167.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 72` of class 167 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 72, core2 := 0, opn := 0 }. -/
theorem F34_c167_k0 : checkChunk 167 n6 cells_167 single_167 links_167 pass_167 open43
    [("2e4383462f92db6b", L6.Certs.C2e4383462f92db6b), ("392aea6662b7eaef", L6.Certs.C392aea6662b7eaef), ("b1a8296b2bd2b206", L6.Certs.Cb1a8296b2bd2b206), ("b8869a68e220593f", L6.Certs.Cb8869a68e220593f)]
    0 72 { single := 0, core1 := 72, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
