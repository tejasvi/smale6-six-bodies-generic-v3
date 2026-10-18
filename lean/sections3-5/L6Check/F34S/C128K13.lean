import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C04a293a6f93a7c21
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C147b955ca1b11d54
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C22fda6d5f8085729
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C2c01c5ebb92665ab
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C3b11b2e3507cfb69
import L6Check.Certs.C48bd81f38eac271c
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C4bda87b2c7299d65
import L6Check.Certs.C4f0c91a1caed7fbb
import L6Check.Certs.C51325aff203d7aed
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C5b0927b744db51b2
import L6Check.Certs.C5c070f2fc555c352
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C64032eea1821e565
import L6Check.Certs.C6f51d187428cfc24
import L6Check.Certs.C718d8795f7c3db3f
import L6Check.Certs.C7470e3f053b22ce6
import L6Check.Certs.C7a5bc61e352bdebf
import L6Check.Certs.C8377f882c1672b34
import L6Check.Certs.C83e997a1e6f21d99
import L6Check.Certs.C8560152d62098be0
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.Ca0e9e314aaa63bd3
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca70957032f7223f5
import L6Check.Certs.Ca852b6f1c1c7de3e
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Cb572ba022f4eb792
import L6Check.Certs.Cb5cd41d059a8288b
import L6Check.Certs.Cbb253f5966cad766
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc31605f52f04f2dc
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cca8aff8c9a441da7
import L6Check.Certs.Ccea573f3b40c98b7
import L6Check.Certs.Cd4d0ff2b2f828bc5
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Cf035dadccade8f55
import L6Check.Certs.Cf20b0193ae6b9e12
import L6Check.Certs.Cf555092f238b9c5a

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 19500 ≤ cell < 21000 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `19500 ≤ cell < 21000` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1064, core1 := 436, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k13 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("04a293a6f93a7c21", L6.Certs.C04a293a6f93a7c21), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("147b955ca1b11d54", L6.Certs.C147b955ca1b11d54), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("22fda6d5f8085729", L6.Certs.C22fda6d5f8085729), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("2c01c5ebb92665ab", L6.Certs.C2c01c5ebb92665ab), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("3b11b2e3507cfb69", L6.Certs.C3b11b2e3507cfb69), ("48bd81f38eac271c", L6.Certs.C48bd81f38eac271c), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("4bda87b2c7299d65", L6.Certs.C4bda87b2c7299d65), ("4f0c91a1caed7fbb", L6.Certs.C4f0c91a1caed7fbb), ("51325aff203d7aed", L6.Certs.C51325aff203d7aed), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("5b0927b744db51b2", L6.Certs.C5b0927b744db51b2), ("5c070f2fc555c352", L6.Certs.C5c070f2fc555c352), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("64032eea1821e565", L6.Certs.C64032eea1821e565), ("6f51d187428cfc24", L6.Certs.C6f51d187428cfc24), ("718d8795f7c3db3f", L6.Certs.C718d8795f7c3db3f), ("7470e3f053b22ce6", L6.Certs.C7470e3f053b22ce6), ("7a5bc61e352bdebf", L6.Certs.C7a5bc61e352bdebf), ("8377f882c1672b34", L6.Certs.C8377f882c1672b34), ("83e997a1e6f21d99", L6.Certs.C83e997a1e6f21d99), ("8560152d62098be0", L6.Certs.C8560152d62098be0), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("a0e9e314aaa63bd3", L6.Certs.Ca0e9e314aaa63bd3), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a70957032f7223f5", L6.Certs.Ca70957032f7223f5), ("a852b6f1c1c7de3e", L6.Certs.Ca852b6f1c1c7de3e), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("b572ba022f4eb792", L6.Certs.Cb572ba022f4eb792), ("b5cd41d059a8288b", L6.Certs.Cb5cd41d059a8288b), ("bb253f5966cad766", L6.Certs.Cbb253f5966cad766), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c31605f52f04f2dc", L6.Certs.Cc31605f52f04f2dc), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("ca8aff8c9a441da7", L6.Certs.Cca8aff8c9a441da7), ("cea573f3b40c98b7", L6.Certs.Ccea573f3b40c98b7), ("d4d0ff2b2f828bc5", L6.Certs.Cd4d0ff2b2f828bc5), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("f035dadccade8f55", L6.Certs.Cf035dadccade8f55), ("f20b0193ae6b9e12", L6.Certs.Cf20b0193ae6b9e12), ("f555092f238b9c5a", L6.Certs.Cf555092f238b9c5a)]
    19500 21000 { single := 1064, core1 := 436, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
