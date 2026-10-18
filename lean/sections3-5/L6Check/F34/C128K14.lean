import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C04a293a6f93a7c21
import L6Check.Certs.C05e400010015c30b
import L6Check.Certs.C0b0cc0f76ff913eb
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1d6c9c68b0b30e0d
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C289c32f09aee0b46
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C30184054f51d9e96
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C4c8e9cfbca25e075
import L6Check.Certs.C4f0c91a1caed7fbb
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C58744aa197893a83
import L6Check.Certs.C5c070f2fc555c352
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C718d8795f7c3db3f
import L6Check.Certs.C724a7accb412014a
import L6Check.Certs.C7470e3f053b22ce6
import L6Check.Certs.C7a5bc61e352bdebf
import L6Check.Certs.C7cb6e6fe7b7130b5
import L6Check.Certs.C83e997a1e6f21d99
import L6Check.Certs.C8560152d62098be0
import L6Check.Certs.C87646cfb8291a9c0
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.Ca0269f9ead157d0c
import L6Check.Certs.Ca70957032f7223f5
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Cb572ba022f4eb792
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cc5e28c7729b266fb
import L6Check.Certs.Ccea573f3b40c98b7
import L6Check.Certs.Cd4d0ff2b2f828bc5
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cda767b1331e531fb
import L6Check.Certs.Cdcc5b5466c47f4da
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Ce37ca8d220a7d5b8
import L6Check.Certs.Ce80b80e4cb5ae9fe
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Cf555092f238b9c5a

/-! F3/F4 (Proposition 5.3), class 128, cells 21000 ≤ cell < 22500 of `data/cells/c128.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `21000 ≤ cell < 22500` of class 128 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1174, core1 := 326, core2 := 0, opn := 0 }. -/
theorem F34_c128_k14 : checkChunk 128 n6 cells_128 single_128 links_128 pass_128 open43
    [("04a293a6f93a7c21", L6.Certs.C04a293a6f93a7c21), ("05e400010015c30b", L6.Certs.C05e400010015c30b), ("0b0cc0f76ff913eb", L6.Certs.C0b0cc0f76ff913eb), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1d6c9c68b0b30e0d", L6.Certs.C1d6c9c68b0b30e0d), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("289c32f09aee0b46", L6.Certs.C289c32f09aee0b46), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("30184054f51d9e96", L6.Certs.C30184054f51d9e96), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("4c8e9cfbca25e075", L6.Certs.C4c8e9cfbca25e075), ("4f0c91a1caed7fbb", L6.Certs.C4f0c91a1caed7fbb), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("58744aa197893a83", L6.Certs.C58744aa197893a83), ("5c070f2fc555c352", L6.Certs.C5c070f2fc555c352), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("718d8795f7c3db3f", L6.Certs.C718d8795f7c3db3f), ("724a7accb412014a", L6.Certs.C724a7accb412014a), ("7470e3f053b22ce6", L6.Certs.C7470e3f053b22ce6), ("7a5bc61e352bdebf", L6.Certs.C7a5bc61e352bdebf), ("7cb6e6fe7b7130b5", L6.Certs.C7cb6e6fe7b7130b5), ("83e997a1e6f21d99", L6.Certs.C83e997a1e6f21d99), ("8560152d62098be0", L6.Certs.C8560152d62098be0), ("87646cfb8291a9c0", L6.Certs.C87646cfb8291a9c0), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("a0269f9ead157d0c", L6.Certs.Ca0269f9ead157d0c), ("a70957032f7223f5", L6.Certs.Ca70957032f7223f5), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("b572ba022f4eb792", L6.Certs.Cb572ba022f4eb792), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("c5e28c7729b266fb", L6.Certs.Cc5e28c7729b266fb), ("cea573f3b40c98b7", L6.Certs.Ccea573f3b40c98b7), ("d4d0ff2b2f828bc5", L6.Certs.Cd4d0ff2b2f828bc5), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("da767b1331e531fb", L6.Certs.Cda767b1331e531fb), ("dcc5b5466c47f4da", L6.Certs.Cdcc5b5466c47f4da), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("e37ca8d220a7d5b8", L6.Certs.Ce37ca8d220a7d5b8), ("e80b80e4cb5ae9fe", L6.Certs.Ce80b80e4cb5ae9fe), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("f555092f238b9c5a", L6.Certs.Cf555092f238b9c5a)]
    21000 22500 { single := 1174, core1 := 326, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
