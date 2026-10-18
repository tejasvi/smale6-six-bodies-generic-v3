import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C148
import L6Check.Certs.C016f78cba46c684e
import L6Check.Certs.C0a4074aebcba0185
import L6Check.Certs.C0d84218e6efa3052
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C1614b3b557ef0fa6
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C2e4383462f92db6b
import L6Check.Certs.C433e02cba79b9834
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C5abeb32d53254fc6
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C7c277ddd83e57eb6
import L6Check.Certs.C7f33f340942be0d0
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.Cb8869a68e220593f
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cc1b12dcb43c4ff0f
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Cf75f12324fc8638c

/-! F3/F4 (Proposition 5.3), class 148, cells 4500 ≤ cell < 4777 of `data/cells/c148.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `4500 ≤ cell < 4777` of class 148 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 251, core1 := 21, core2 := 5, opn := 0 }. -/
theorem F34_c148_k3 : checkChunk 148 n6 cells_148 single_148 links_148 pass_148 open43
    [("016f78cba46c684e", L6.Certs.C016f78cba46c684e), ("0a4074aebcba0185", L6.Certs.C0a4074aebcba0185), ("0d84218e6efa3052", L6.Certs.C0d84218e6efa3052), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("1614b3b557ef0fa6", L6.Certs.C1614b3b557ef0fa6), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("2e4383462f92db6b", L6.Certs.C2e4383462f92db6b), ("433e02cba79b9834", L6.Certs.C433e02cba79b9834), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("5abeb32d53254fc6", L6.Certs.C5abeb32d53254fc6), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("7c277ddd83e57eb6", L6.Certs.C7c277ddd83e57eb6), ("7f33f340942be0d0", L6.Certs.C7f33f340942be0d0), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("b8869a68e220593f", L6.Certs.Cb8869a68e220593f), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("c1b12dcb43c4ff0f", L6.Certs.Cc1b12dcb43c4ff0f), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("f75f12324fc8638c", L6.Certs.Cf75f12324fc8638c)]
    4500 4777 { single := 251, core1 := 21, core2 := 5, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
