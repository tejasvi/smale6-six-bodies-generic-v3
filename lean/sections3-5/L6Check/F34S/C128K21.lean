import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C05b8f74d17bf797e
import L6Check.Certs.C062f626c7e3da160
import L6Check.Certs.C0726ad90b7fe118d
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C16c607738140b7f4
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1929243d69119efb
import L6Check.Certs.C2541da28357df072
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C549547755e1f7a45
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C5c070f2fc555c352
import L6Check.Certs.C60742c0aa412da86
import L6Check.Certs.C6d7de0cc1be131cc
import L6Check.Certs.C6f900cd2293a5d9f
import L6Check.Certs.C6ff53cb44584c94d
import L6Check.Certs.C7972111a1147fdc1
import L6Check.Certs.C98d57d5231d8f193
import L6Check.Certs.C99554a2fc1aa3180
import L6Check.Certs.C9994472ee3a3df0a
import L6Check.Certs.C9afc567d75a8e62c
import L6Check.Certs.C9f7972664b835613
import L6Check.Certs.Ca1c2e7d7424df28c
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cb4b79584ea6a83a1
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc51438b9ccf4edfb
import L6Check.Certs.Cc7f832c444000333
import L6Check.Certs.Cd363b7180a66c9b5
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce11b7354ea07bda3
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Cea48080a5c1435fc
import L6Check.Certs.Cf308512ed9e141fb
import L6Check.Certs.Cf75f12324fc8638c
import L6Check.Certs.Cfb26a2f26815b2d8

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 31500 ≤ cell < 32864 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `31500 ≤ cell < 32864` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1124, core1 := 240, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k21 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("05b8f74d17bf797e", L6.Certs.C05b8f74d17bf797e), ("062f626c7e3da160", L6.Certs.C062f626c7e3da160), ("0726ad90b7fe118d", L6.Certs.C0726ad90b7fe118d), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("16c607738140b7f4", L6.Certs.C16c607738140b7f4), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1929243d69119efb", L6.Certs.C1929243d69119efb), ("2541da28357df072", L6.Certs.C2541da28357df072), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("549547755e1f7a45", L6.Certs.C549547755e1f7a45), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("5c070f2fc555c352", L6.Certs.C5c070f2fc555c352), ("60742c0aa412da86", L6.Certs.C60742c0aa412da86), ("6d7de0cc1be131cc", L6.Certs.C6d7de0cc1be131cc), ("6f900cd2293a5d9f", L6.Certs.C6f900cd2293a5d9f), ("6ff53cb44584c94d", L6.Certs.C6ff53cb44584c94d), ("7972111a1147fdc1", L6.Certs.C7972111a1147fdc1), ("98d57d5231d8f193", L6.Certs.C98d57d5231d8f193), ("99554a2fc1aa3180", L6.Certs.C99554a2fc1aa3180), ("9994472ee3a3df0a", L6.Certs.C9994472ee3a3df0a), ("9afc567d75a8e62c", L6.Certs.C9afc567d75a8e62c), ("9f7972664b835613", L6.Certs.C9f7972664b835613), ("a1c2e7d7424df28c", L6.Certs.Ca1c2e7d7424df28c), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("b4b79584ea6a83a1", L6.Certs.Cb4b79584ea6a83a1), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c51438b9ccf4edfb", L6.Certs.Cc51438b9ccf4edfb), ("c7f832c444000333", L6.Certs.Cc7f832c444000333), ("d363b7180a66c9b5", L6.Certs.Cd363b7180a66c9b5), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e11b7354ea07bda3", L6.Certs.Ce11b7354ea07bda3), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("ea48080a5c1435fc", L6.Certs.Cea48080a5c1435fc), ("f308512ed9e141fb", L6.Certs.Cf308512ed9e141fb), ("f75f12324fc8638c", L6.Certs.Cf75f12324fc8638c), ("fb26a2f26815b2d8", L6.Certs.Cfb26a2f26815b2d8)]
    31500 32864 { single := 1124, core1 := 240, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
