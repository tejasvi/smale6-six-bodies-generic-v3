import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C149
import L6Check.F34.Data.Common
import L6Check.F34.Data.C149
import L6Check.Certs.C078dea9c27658ce0
import L6Check.Certs.C085a33b7d1d675c9
import L6Check.Certs.C0eb88f70e19c3651
import L6Check.Certs.C13a2d4f340860d49
import L6Check.Certs.C19766c038a4f930e
import L6Check.Certs.C1a8244464645923c
import L6Check.Certs.C1eff0665cbb41292
import L6Check.Certs.C22a4a3c90f34e0db
import L6Check.Certs.C2f371fd473f0159b
import L6Check.Certs.C3512e87dbd770078
import L6Check.Certs.C37c58de9b6470767
import L6Check.Certs.C39cab825bf3d8730
import L6Check.Certs.C45d6afadfad43b3f
import L6Check.Certs.C4e77f5f512983c9f
import L6Check.Certs.C508fa2210e538bd7
import L6Check.Certs.C51a136f020a20690
import L6Check.Certs.C553c67900281f55f
import L6Check.Certs.C57b00b6081bb0cf0
import L6Check.Certs.C58d79838d4f69573
import L6Check.Certs.C591dad9a9e121435
import L6Check.Certs.C60e5b32266737d07
import L6Check.Certs.C6696a0e7a16f0761
import L6Check.Certs.C673f4c906c05435d
import L6Check.Certs.C68c1a1002cc774a2
import L6Check.Certs.C6995f0d169b9eb90
import L6Check.Certs.C75d8263ef29760f8
import L6Check.Certs.C7a98202209d08e42
import L6Check.Certs.C818e3de2a8fadb22
import L6Check.Certs.C86d4bd4e9d49c687
import L6Check.Certs.C8884b9f860044245
import L6Check.Certs.C88df84ea194b1ba9
import L6Check.Certs.C950a06bff383f88c
import L6Check.Certs.C97a15cde3c5e23ad
import L6Check.Certs.C98f8948c205c615f
import L6Check.Certs.C9ac00a0e2a528e7c
import L6Check.Certs.C9f8d23b506ee412a
import L6Check.Certs.Ca123b4dbf9561825
import L6Check.Certs.Ca3f8535a45468560
import L6Check.Certs.Ca6ddcd4d8be768b9
import L6Check.Certs.Ca91cbe472069c6c1
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cb59ea9126752a36f
import L6Check.Certs.Cbce719b84d6df6d2
import L6Check.Certs.Cbd29b30d5ea8dde7
import L6Check.Certs.Cbe8af43fa23c31ee
import L6Check.Certs.Cbecb8ae0ffae3b77
import L6Check.Certs.Cbf128e8148a3614d
import L6Check.Certs.Cc26c0f37ef7e8ebb
import L6Check.Certs.Cc7178650eff5f38a
import L6Check.Certs.Cca083f86e77fc3e8
import L6Check.Certs.Cd03c4e4bf35ccb2e
import L6Check.Certs.Cdd9300dbab7e39e2
import L6Check.Certs.Cde13238c8be61fb2
import L6Check.Certs.Ce0b5a07c13e465a7
import L6Check.Certs.Ce10fa29e187952bc
import L6Check.Certs.Ce7d7ef80145aa9c0
import L6Check.Certs.Cef0a3bb49c97bcc0
import L6Check.Certs.Cf0cccaca3ee113dc
import L6Check.Certs.Cf1c0efc1e2010891
import L6Check.Certs.Cf33c5e22806fdf48
import L6Check.Certs.Cfa1cf161378efd22
import L6Check.Certs.Cfa814e2fdf6b9531
import L6Check.Certs.Cfe7be52825bd66c8

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 149, cells 0 ≤ cell < 756 of
`data/cells/c149.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 756` of class 149 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 420, core1 := 280, core2 := 56, opn := 0 }. -/
theorem F34S_c149_k0 : checkChunkS 149 (L6.F2.diagOf 149) L6.F2.Data.cells_c149 single_149 links_149 pass_149 open43
    [("078dea9c27658ce0", L6.Certs.C078dea9c27658ce0), ("085a33b7d1d675c9", L6.Certs.C085a33b7d1d675c9), ("0eb88f70e19c3651", L6.Certs.C0eb88f70e19c3651), ("13a2d4f340860d49", L6.Certs.C13a2d4f340860d49), ("19766c038a4f930e", L6.Certs.C19766c038a4f930e), ("1a8244464645923c", L6.Certs.C1a8244464645923c), ("1eff0665cbb41292", L6.Certs.C1eff0665cbb41292), ("22a4a3c90f34e0db", L6.Certs.C22a4a3c90f34e0db), ("2f371fd473f0159b", L6.Certs.C2f371fd473f0159b), ("3512e87dbd770078", L6.Certs.C3512e87dbd770078), ("37c58de9b6470767", L6.Certs.C37c58de9b6470767), ("39cab825bf3d8730", L6.Certs.C39cab825bf3d8730), ("45d6afadfad43b3f", L6.Certs.C45d6afadfad43b3f), ("4e77f5f512983c9f", L6.Certs.C4e77f5f512983c9f), ("508fa2210e538bd7", L6.Certs.C508fa2210e538bd7), ("51a136f020a20690", L6.Certs.C51a136f020a20690), ("553c67900281f55f", L6.Certs.C553c67900281f55f), ("57b00b6081bb0cf0", L6.Certs.C57b00b6081bb0cf0), ("58d79838d4f69573", L6.Certs.C58d79838d4f69573), ("591dad9a9e121435", L6.Certs.C591dad9a9e121435), ("60e5b32266737d07", L6.Certs.C60e5b32266737d07), ("6696a0e7a16f0761", L6.Certs.C6696a0e7a16f0761), ("673f4c906c05435d", L6.Certs.C673f4c906c05435d), ("68c1a1002cc774a2", L6.Certs.C68c1a1002cc774a2), ("6995f0d169b9eb90", L6.Certs.C6995f0d169b9eb90), ("75d8263ef29760f8", L6.Certs.C75d8263ef29760f8), ("7a98202209d08e42", L6.Certs.C7a98202209d08e42), ("818e3de2a8fadb22", L6.Certs.C818e3de2a8fadb22), ("86d4bd4e9d49c687", L6.Certs.C86d4bd4e9d49c687), ("8884b9f860044245", L6.Certs.C8884b9f860044245), ("88df84ea194b1ba9", L6.Certs.C88df84ea194b1ba9), ("950a06bff383f88c", L6.Certs.C950a06bff383f88c), ("97a15cde3c5e23ad", L6.Certs.C97a15cde3c5e23ad), ("98f8948c205c615f", L6.Certs.C98f8948c205c615f), ("9ac00a0e2a528e7c", L6.Certs.C9ac00a0e2a528e7c), ("9f8d23b506ee412a", L6.Certs.C9f8d23b506ee412a), ("a123b4dbf9561825", L6.Certs.Ca123b4dbf9561825), ("a3f8535a45468560", L6.Certs.Ca3f8535a45468560), ("a6ddcd4d8be768b9", L6.Certs.Ca6ddcd4d8be768b9), ("a91cbe472069c6c1", L6.Certs.Ca91cbe472069c6c1), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("b59ea9126752a36f", L6.Certs.Cb59ea9126752a36f), ("bce719b84d6df6d2", L6.Certs.Cbce719b84d6df6d2), ("bd29b30d5ea8dde7", L6.Certs.Cbd29b30d5ea8dde7), ("be8af43fa23c31ee", L6.Certs.Cbe8af43fa23c31ee), ("becb8ae0ffae3b77", L6.Certs.Cbecb8ae0ffae3b77), ("bf128e8148a3614d", L6.Certs.Cbf128e8148a3614d), ("c26c0f37ef7e8ebb", L6.Certs.Cc26c0f37ef7e8ebb), ("c7178650eff5f38a", L6.Certs.Cc7178650eff5f38a), ("ca083f86e77fc3e8", L6.Certs.Cca083f86e77fc3e8), ("d03c4e4bf35ccb2e", L6.Certs.Cd03c4e4bf35ccb2e), ("dd9300dbab7e39e2", L6.Certs.Cdd9300dbab7e39e2), ("de13238c8be61fb2", L6.Certs.Cde13238c8be61fb2), ("e0b5a07c13e465a7", L6.Certs.Ce0b5a07c13e465a7), ("e10fa29e187952bc", L6.Certs.Ce10fa29e187952bc), ("e7d7ef80145aa9c0", L6.Certs.Ce7d7ef80145aa9c0), ("ef0a3bb49c97bcc0", L6.Certs.Cef0a3bb49c97bcc0), ("f0cccaca3ee113dc", L6.Certs.Cf0cccaca3ee113dc), ("f1c0efc1e2010891", L6.Certs.Cf1c0efc1e2010891), ("f33c5e22806fdf48", L6.Certs.Cf33c5e22806fdf48), ("fa1cf161378efd22", L6.Certs.Cfa1cf161378efd22), ("fa814e2fdf6b9531", L6.Certs.Cfa814e2fdf6b9531), ("fe7be52825bd66c8", L6.Certs.Cfe7be52825bd66c8)]
    0 756 { single := 420, core1 := 280, core2 := 56, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
