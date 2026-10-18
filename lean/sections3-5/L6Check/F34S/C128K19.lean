import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C0b0cc0f76ff913eb
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1929243d69119efb
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C289c32f09aee0b46
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C30184054f51d9e96
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C4c8e9cfbca25e075
import L6Check.Certs.C51ee843597cff9f3
import L6Check.Certs.C549547755e1f7a45
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C58744aa197893a83
import L6Check.Certs.C5c070f2fc555c352
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C6f900cd2293a5d9f
import L6Check.Certs.C724a7accb412014a
import L6Check.Certs.C7cb6e6fe7b7130b5
import L6Check.Certs.C87646cfb8291a9c0
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C98d57d5231d8f193
import L6Check.Certs.C9afc567d75a8e62c
import L6Check.Certs.C9f7972664b835613
import L6Check.Certs.Ca0269f9ead157d0c
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Cb4b79584ea6a83a1
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cc7f832c444000333
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cda767b1331e531fb
import L6Check.Certs.Cdcc5b5466c47f4da
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Ce37ca8d220a7d5b8
import L6Check.Certs.Ce80b80e4cb5ae9fe
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Cfab0e5212c8d3c79

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 28500 ≤ cell < 30000 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `28500 ≤ cell < 30000` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1242, core1 := 258, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k19 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("0b0cc0f76ff913eb", L6.Certs.C0b0cc0f76ff913eb), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1929243d69119efb", L6.Certs.C1929243d69119efb), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("289c32f09aee0b46", L6.Certs.C289c32f09aee0b46), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("30184054f51d9e96", L6.Certs.C30184054f51d9e96), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("4c8e9cfbca25e075", L6.Certs.C4c8e9cfbca25e075), ("51ee843597cff9f3", L6.Certs.C51ee843597cff9f3), ("549547755e1f7a45", L6.Certs.C549547755e1f7a45), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("58744aa197893a83", L6.Certs.C58744aa197893a83), ("5c070f2fc555c352", L6.Certs.C5c070f2fc555c352), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("6f900cd2293a5d9f", L6.Certs.C6f900cd2293a5d9f), ("724a7accb412014a", L6.Certs.C724a7accb412014a), ("7cb6e6fe7b7130b5", L6.Certs.C7cb6e6fe7b7130b5), ("87646cfb8291a9c0", L6.Certs.C87646cfb8291a9c0), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("98d57d5231d8f193", L6.Certs.C98d57d5231d8f193), ("9afc567d75a8e62c", L6.Certs.C9afc567d75a8e62c), ("9f7972664b835613", L6.Certs.C9f7972664b835613), ("a0269f9ead157d0c", L6.Certs.Ca0269f9ead157d0c), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("b4b79584ea6a83a1", L6.Certs.Cb4b79584ea6a83a1), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("c7f832c444000333", L6.Certs.Cc7f832c444000333), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("da767b1331e531fb", L6.Certs.Cda767b1331e531fb), ("dcc5b5466c47f4da", L6.Certs.Cdcc5b5466c47f4da), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("e37ca8d220a7d5b8", L6.Certs.Ce37ca8d220a7d5b8), ("e80b80e4cb5ae9fe", L6.Certs.Ce80b80e4cb5ae9fe), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("fab0e5212c8d3c79", L6.Certs.Cfab0e5212c8d3c79)]
    28500 30000 { single := 1242, core1 := 258, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
