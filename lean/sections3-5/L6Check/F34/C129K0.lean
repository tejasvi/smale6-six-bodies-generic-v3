import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C129
import L6Check.Certs.C1e35066014af680f
import L6Check.Certs.C2f1462ab17a0f370
import L6Check.Certs.C340899552eaac01d
import L6Check.Certs.C44b11fbc9a933503
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C661441e082bf5fdc
import L6Check.Certs.C8185764ed1fa3d6a
import L6Check.Certs.C830035da5f0a64db
import L6Check.Certs.C9dcc5b5558322086
import L6Check.Certs.Cb0798c2bf2ea25ad
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cf3c6f2a09e8ae40d
import L6Check.Certs.Cf8436c57798d2400

/-! F3/F4 (Proposition 5.3), class 129, cells 0 ≤ cell < 1449 of `data/cells/c129.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1449` of class 129 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 924, core1 := 525, core2 := 0, opn := 0 }. -/
theorem F34_c129_k0 : checkChunk 129 n6 cells_129 single_129 links_129 pass_129 open43
    [("1e35066014af680f", L6.Certs.C1e35066014af680f), ("2f1462ab17a0f370", L6.Certs.C2f1462ab17a0f370), ("340899552eaac01d", L6.Certs.C340899552eaac01d), ("44b11fbc9a933503", L6.Certs.C44b11fbc9a933503), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("661441e082bf5fdc", L6.Certs.C661441e082bf5fdc), ("8185764ed1fa3d6a", L6.Certs.C8185764ed1fa3d6a), ("830035da5f0a64db", L6.Certs.C830035da5f0a64db), ("9dcc5b5558322086", L6.Certs.C9dcc5b5558322086), ("b0798c2bf2ea25ad", L6.Certs.Cb0798c2bf2ea25ad), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("f3c6f2a09e8ae40d", L6.Certs.Cf3c6f2a09e8ae40d), ("f8436c57798d2400", L6.Certs.Cf8436c57798d2400)]
    0 1449 { single := 924, core1 := 525, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
