import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C04a293a6f93a7c21
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C147b955ca1b11d54
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C2c01c5ebb92665ab
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C2d98fc5276cebdd8
import L6Check.Certs.C376b718487da742b
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C46bb7d1d47186aa8
import L6Check.Certs.C48bd81f38eac271c
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C4f0c91a1caed7fbb
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C5b0927b744db51b2
import L6Check.Certs.C5c070f2fc555c352
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C60742c0aa412da86
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C6f51d187428cfc24
import L6Check.Certs.C718d8795f7c3db3f
import L6Check.Certs.C7470e3f053b22ce6
import L6Check.Certs.C7972111a1147fdc1
import L6Check.Certs.C7a5bc61e352bdebf
import L6Check.Certs.C8377f882c1672b34
import L6Check.Certs.C83e997a1e6f21d99
import L6Check.Certs.C8560152d62098be0
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C93549b380527c3e0
import L6Check.Certs.C9b5cd75375f980af
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Ca70957032f7223f5
import L6Check.Certs.Ca852b6f1c1c7de3e
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Cb33ea2b4c1c341f9
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Cb572ba022f4eb792
import L6Check.Certs.Cb5cd41d059a8288b
import L6Check.Certs.Cbb253f5966cad766
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cbf1c1072d313dea1
import L6Check.Certs.Cbf27248691902ac4
import L6Check.Certs.Cc283f4873b50bcb4
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Ccea573f3b40c98b7
import L6Check.Certs.Cd4d0ff2b2f828bc5
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Cefbdadd3a9fafcff
import L6Check.Certs.Cf20b0193ae6b9e12
import L6Check.Certs.Cf9e213c51db3acef
import L6Check.Certs.Cfb26a2f26815b2d8

/-! F3/F4 (Proposition 5.3), class 128, cells 18000 ≤ cell < 19500 of `data/cells/c128.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `18000 ≤ cell < 19500` of class 128 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1122, core1 := 378, core2 := 0, opn := 0 }. -/
theorem F34_c128_k12 : checkChunk 128 n6 cells_128 single_128 links_128 pass_128 open43
    [("04a293a6f93a7c21", L6.Certs.C04a293a6f93a7c21), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("147b955ca1b11d54", L6.Certs.C147b955ca1b11d54), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("2c01c5ebb92665ab", L6.Certs.C2c01c5ebb92665ab), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("2d98fc5276cebdd8", L6.Certs.C2d98fc5276cebdd8), ("376b718487da742b", L6.Certs.C376b718487da742b), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("46bb7d1d47186aa8", L6.Certs.C46bb7d1d47186aa8), ("48bd81f38eac271c", L6.Certs.C48bd81f38eac271c), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("4f0c91a1caed7fbb", L6.Certs.C4f0c91a1caed7fbb), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("5b0927b744db51b2", L6.Certs.C5b0927b744db51b2), ("5c070f2fc555c352", L6.Certs.C5c070f2fc555c352), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("60742c0aa412da86", L6.Certs.C60742c0aa412da86), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("6f51d187428cfc24", L6.Certs.C6f51d187428cfc24), ("718d8795f7c3db3f", L6.Certs.C718d8795f7c3db3f), ("7470e3f053b22ce6", L6.Certs.C7470e3f053b22ce6), ("7972111a1147fdc1", L6.Certs.C7972111a1147fdc1), ("7a5bc61e352bdebf", L6.Certs.C7a5bc61e352bdebf), ("8377f882c1672b34", L6.Certs.C8377f882c1672b34), ("83e997a1e6f21d99", L6.Certs.C83e997a1e6f21d99), ("8560152d62098be0", L6.Certs.C8560152d62098be0), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("93549b380527c3e0", L6.Certs.C93549b380527c3e0), ("9b5cd75375f980af", L6.Certs.C9b5cd75375f980af), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("a70957032f7223f5", L6.Certs.Ca70957032f7223f5), ("a852b6f1c1c7de3e", L6.Certs.Ca852b6f1c1c7de3e), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("b33ea2b4c1c341f9", L6.Certs.Cb33ea2b4c1c341f9), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("b572ba022f4eb792", L6.Certs.Cb572ba022f4eb792), ("b5cd41d059a8288b", L6.Certs.Cb5cd41d059a8288b), ("bb253f5966cad766", L6.Certs.Cbb253f5966cad766), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("bf1c1072d313dea1", L6.Certs.Cbf1c1072d313dea1), ("bf27248691902ac4", L6.Certs.Cbf27248691902ac4), ("c283f4873b50bcb4", L6.Certs.Cc283f4873b50bcb4), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("cea573f3b40c98b7", L6.Certs.Ccea573f3b40c98b7), ("d4d0ff2b2f828bc5", L6.Certs.Cd4d0ff2b2f828bc5), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("efbdadd3a9fafcff", L6.Certs.Cefbdadd3a9fafcff), ("f20b0193ae6b9e12", L6.Certs.Cf20b0193ae6b9e12), ("f9e213c51db3acef", L6.Certs.Cf9e213c51db3acef), ("fb26a2f26815b2d8", L6.Certs.Cfb26a2f26815b2d8)]
    18000 19500 { single := 1122, core1 := 378, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
