import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C44
import L6Check.Certs.C033bc82030d83f02
import L6Check.Certs.C241fc1f51e91d096
import L6Check.Certs.C3fd24f1da5fde363
import L6Check.Certs.C596191694178d9f3
import L6Check.Certs.C5c9231ea55c64021
import L6Check.Certs.C72e4fa5572231661
import L6Check.Certs.C7b62fb6652252e5d
import L6Check.Certs.C8d403b01ab872d2c
import L6Check.Certs.Ca137255f8b3b67f4
import L6Check.Certs.Ca803305cad9560c4
import L6Check.Certs.Cb7c456ec07072ed7
import L6Check.Certs.Ce4c0b509d57d72c5
import L6Check.Certs.Cffbf722c0be74172

/-! F3/F4 (Proposition 5.3), class 44, cells 0 ≤ cell < 154 of `data/cells/c44.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 154` of class 44 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 7, core1 := 147, core2 := 0, opn := 0 }. -/
theorem F34_c44_k0 : checkChunk 44 n6 cells_44 single_44 links_44 pass_44 open43
    [("033bc82030d83f02", L6.Certs.C033bc82030d83f02), ("241fc1f51e91d096", L6.Certs.C241fc1f51e91d096), ("3fd24f1da5fde363", L6.Certs.C3fd24f1da5fde363), ("596191694178d9f3", L6.Certs.C596191694178d9f3), ("5c9231ea55c64021", L6.Certs.C5c9231ea55c64021), ("72e4fa5572231661", L6.Certs.C72e4fa5572231661), ("7b62fb6652252e5d", L6.Certs.C7b62fb6652252e5d), ("8d403b01ab872d2c", L6.Certs.C8d403b01ab872d2c), ("a137255f8b3b67f4", L6.Certs.Ca137255f8b3b67f4), ("a803305cad9560c4", L6.Certs.Ca803305cad9560c4), ("b7c456ec07072ed7", L6.Certs.Cb7c456ec07072ed7), ("e4c0b509d57d72c5", L6.Certs.Ce4c0b509d57d72c5), ("ffbf722c0be74172", L6.Certs.Cffbf722c0be74172)]
    0 154 { single := 7, core1 := 147, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
