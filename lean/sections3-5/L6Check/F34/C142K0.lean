import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C142
import L6Check.Certs.C04b1474bc3439753
import L6Check.Certs.C0a4074aebcba0185
import L6Check.Certs.C2e4383462f92db6b
import L6Check.Certs.C51ee843597cff9f3
import L6Check.Certs.C549547755e1f7a45
import L6Check.Certs.C58744aa197893a83
import L6Check.Certs.C6b315134a56bc14d
import L6Check.Certs.C6f900cd2293a5d9f
import L6Check.Certs.C7a5bc61e352bdebf
import L6Check.Certs.C9dcd6685d79bf841
import L6Check.Certs.C9f7972664b835613
import L6Check.Certs.Ca0269f9ead157d0c
import L6Check.Certs.Cb4b79584ea6a83a1
import L6Check.Certs.Cb572ba022f4eb792
import L6Check.Certs.Cc7f832c444000333
import L6Check.Certs.Cd4d0ff2b2f828bc5
import L6Check.Certs.Cd5e5dcae6e1dc761
import L6Check.Certs.Ceba34457a14fde28
import L6Check.Certs.Cf555092f238b9c5a
import L6Check.Certs.Cfd3d98c55b1bc4fa

/-! F3/F4 (Proposition 5.3), class 142, cells 0 ≤ cell < 297 of `data/cells/c142.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 297` of class 142 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 189, core1 := 108, core2 := 0, opn := 0 }. -/
theorem F34_c142_k0 : checkChunk 142 n6 cells_142 single_142 links_142 pass_142 open43
    [("04b1474bc3439753", L6.Certs.C04b1474bc3439753), ("0a4074aebcba0185", L6.Certs.C0a4074aebcba0185), ("2e4383462f92db6b", L6.Certs.C2e4383462f92db6b), ("51ee843597cff9f3", L6.Certs.C51ee843597cff9f3), ("549547755e1f7a45", L6.Certs.C549547755e1f7a45), ("58744aa197893a83", L6.Certs.C58744aa197893a83), ("6b315134a56bc14d", L6.Certs.C6b315134a56bc14d), ("6f900cd2293a5d9f", L6.Certs.C6f900cd2293a5d9f), ("7a5bc61e352bdebf", L6.Certs.C7a5bc61e352bdebf), ("9dcd6685d79bf841", L6.Certs.C9dcd6685d79bf841), ("9f7972664b835613", L6.Certs.C9f7972664b835613), ("a0269f9ead157d0c", L6.Certs.Ca0269f9ead157d0c), ("b4b79584ea6a83a1", L6.Certs.Cb4b79584ea6a83a1), ("b572ba022f4eb792", L6.Certs.Cb572ba022f4eb792), ("c7f832c444000333", L6.Certs.Cc7f832c444000333), ("d4d0ff2b2f828bc5", L6.Certs.Cd4d0ff2b2f828bc5), ("d5e5dcae6e1dc761", L6.Certs.Cd5e5dcae6e1dc761), ("eba34457a14fde28", L6.Certs.Ceba34457a14fde28), ("f555092f238b9c5a", L6.Certs.Cf555092f238b9c5a), ("fd3d98c55b1bc4fa", L6.Certs.Cfd3d98c55b1bc4fa)]
    0 297 { single := 189, core1 := 108, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
