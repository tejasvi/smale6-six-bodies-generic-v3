import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C4
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C417511092a5c791b
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca79ff001c9051e4d
import L6Check.Certs.Cf64ab3339f8f6001

/-! F3/F4 (Proposition 5.3), class 4, cells 0 ≤ cell < 177 of `data/cells/c4.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 177` of class 4 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 154, core1 := 23, core2 := 0, opn := 0 }. -/
theorem F34_c4_k0 : checkChunk 4 n6 cells_4 single_4 links_4 pass_4 open43
    [("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("417511092a5c791b", L6.Certs.C417511092a5c791b), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a79ff001c9051e4d", L6.Certs.Ca79ff001c9051e4d), ("f64ab3339f8f6001", L6.Certs.Cf64ab3339f8f6001)]
    0 177 { single := 154, core1 := 23, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
