import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C04b1474bc3439753
import L6Check.Certs.C097ff874790574e3
import L6Check.Certs.C09928f1edf384246
import L6Check.Certs.C0b0cc0f76ff913eb
import L6Check.Certs.C1122637199b86e3e
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C11b1691f381e26bc
import L6Check.Certs.C1340a3de36e54646
import L6Check.Certs.C13834eef33bc2d52
import L6Check.Certs.C15617350d777485d
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C19e3c019fbfb7ff3
import L6Check.Certs.C1f20b9066e9a6fb3
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C289c32f09aee0b46
import L6Check.Certs.C2b350c00b20c97b4
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C30184054f51d9e96
import L6Check.Certs.C3153b8db38d9bcd0
import L6Check.Certs.C362793ab65c827f6
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C3ca9e7b3ada442ed
import L6Check.Certs.C47ecb03a85136af9
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C4a11f8ac23ba9135
import L6Check.Certs.C4b3d156e06797a24
import L6Check.Certs.C4c8e9cfbca25e075
import L6Check.Certs.C51ee843597cff9f3
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C5783f922e65f69eb
import L6Check.Certs.C5c070f2fc555c352
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C619cbdd1f991b7f1
import L6Check.Certs.C6dbd943f90ff0dba
import L6Check.Certs.C71fa860badcbd848
import L6Check.Certs.C7758d47761d69fc2
import L6Check.Certs.C7cb6e6fe7b7130b5
import L6Check.Certs.C7e81da8e9ca061e5
import L6Check.Certs.C80dc6294a3a091ea
import L6Check.Certs.C840c96f3ce3e4567
import L6Check.Certs.C87646cfb8291a9c0
import L6Check.Certs.C90559a3fe54d142b
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C9c6c9f623778d794
import L6Check.Certs.Ca0269f9ead157d0c
import L6Check.Certs.Ca520cec9a3210ed0
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Caf1fed30ea4811fe
import L6Check.Certs.Cb0009b5ada53fae4
import L6Check.Certs.Cb059509bb18b082c
import L6Check.Certs.Cb0f2ec21e41f52f0
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Cba31ca3458e0bd99
import L6Check.Certs.Cbd3f2204d9517b24
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc2efcefe5057bc76
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cc75eb9472f896101
import L6Check.Certs.Cd31feb5406558fe4
import L6Check.Certs.Cd72c58cb5562447e
import L6Check.Certs.Cd9f341d28852700e
import L6Check.Certs.Cda6cee4a2afc7687
import L6Check.Certs.Cda767b1331e531fb
import L6Check.Certs.Cdcc5b5466c47f4da
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Ce35b906803a52334
import L6Check.Certs.Ce37ca8d220a7d5b8
import L6Check.Certs.Ceb42df4682c799fd
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Cf164f74fdb391d6f
import L6Check.Certs.Cf1e9fa064084d512
import L6Check.Certs.Cf6d365aab0daf77f
import L6Check.Certs.Cfbfb6aade07413b6
import L6Check.Certs.Cfc4b1268cbf99c5f
import L6Check.Certs.Cfd4d5e4dd019e4eb

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 7500 ≤ cell < 9000 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `7500 ≤ cell < 9000` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 397, core1 := 1103, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k5 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("04b1474bc3439753", L6.Certs.C04b1474bc3439753), ("097ff874790574e3", L6.Certs.C097ff874790574e3), ("09928f1edf384246", L6.Certs.C09928f1edf384246), ("0b0cc0f76ff913eb", L6.Certs.C0b0cc0f76ff913eb), ("1122637199b86e3e", L6.Certs.C1122637199b86e3e), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("11b1691f381e26bc", L6.Certs.C11b1691f381e26bc), ("1340a3de36e54646", L6.Certs.C1340a3de36e54646), ("13834eef33bc2d52", L6.Certs.C13834eef33bc2d52), ("15617350d777485d", L6.Certs.C15617350d777485d), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("19e3c019fbfb7ff3", L6.Certs.C19e3c019fbfb7ff3), ("1f20b9066e9a6fb3", L6.Certs.C1f20b9066e9a6fb3), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("289c32f09aee0b46", L6.Certs.C289c32f09aee0b46), ("2b350c00b20c97b4", L6.Certs.C2b350c00b20c97b4), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("30184054f51d9e96", L6.Certs.C30184054f51d9e96), ("3153b8db38d9bcd0", L6.Certs.C3153b8db38d9bcd0), ("362793ab65c827f6", L6.Certs.C362793ab65c827f6), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("3ca9e7b3ada442ed", L6.Certs.C3ca9e7b3ada442ed), ("47ecb03a85136af9", L6.Certs.C47ecb03a85136af9), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("4a11f8ac23ba9135", L6.Certs.C4a11f8ac23ba9135), ("4b3d156e06797a24", L6.Certs.C4b3d156e06797a24), ("4c8e9cfbca25e075", L6.Certs.C4c8e9cfbca25e075), ("51ee843597cff9f3", L6.Certs.C51ee843597cff9f3), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("5783f922e65f69eb", L6.Certs.C5783f922e65f69eb), ("5c070f2fc555c352", L6.Certs.C5c070f2fc555c352), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("619cbdd1f991b7f1", L6.Certs.C619cbdd1f991b7f1), ("6dbd943f90ff0dba", L6.Certs.C6dbd943f90ff0dba), ("71fa860badcbd848", L6.Certs.C71fa860badcbd848), ("7758d47761d69fc2", L6.Certs.C7758d47761d69fc2), ("7cb6e6fe7b7130b5", L6.Certs.C7cb6e6fe7b7130b5), ("7e81da8e9ca061e5", L6.Certs.C7e81da8e9ca061e5), ("80dc6294a3a091ea", L6.Certs.C80dc6294a3a091ea), ("840c96f3ce3e4567", L6.Certs.C840c96f3ce3e4567), ("87646cfb8291a9c0", L6.Certs.C87646cfb8291a9c0), ("90559a3fe54d142b", L6.Certs.C90559a3fe54d142b), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("9c6c9f623778d794", L6.Certs.C9c6c9f623778d794), ("a0269f9ead157d0c", L6.Certs.Ca0269f9ead157d0c), ("a520cec9a3210ed0", L6.Certs.Ca520cec9a3210ed0), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("af1fed30ea4811fe", L6.Certs.Caf1fed30ea4811fe), ("b0009b5ada53fae4", L6.Certs.Cb0009b5ada53fae4), ("b059509bb18b082c", L6.Certs.Cb059509bb18b082c), ("b0f2ec21e41f52f0", L6.Certs.Cb0f2ec21e41f52f0), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("ba31ca3458e0bd99", L6.Certs.Cba31ca3458e0bd99), ("bd3f2204d9517b24", L6.Certs.Cbd3f2204d9517b24), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c2efcefe5057bc76", L6.Certs.Cc2efcefe5057bc76), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("c75eb9472f896101", L6.Certs.Cc75eb9472f896101), ("d31feb5406558fe4", L6.Certs.Cd31feb5406558fe4), ("d72c58cb5562447e", L6.Certs.Cd72c58cb5562447e), ("d9f341d28852700e", L6.Certs.Cd9f341d28852700e), ("da6cee4a2afc7687", L6.Certs.Cda6cee4a2afc7687), ("da767b1331e531fb", L6.Certs.Cda767b1331e531fb), ("dcc5b5466c47f4da", L6.Certs.Cdcc5b5466c47f4da), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("e35b906803a52334", L6.Certs.Ce35b906803a52334), ("e37ca8d220a7d5b8", L6.Certs.Ce37ca8d220a7d5b8), ("eb42df4682c799fd", L6.Certs.Ceb42df4682c799fd), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("f164f74fdb391d6f", L6.Certs.Cf164f74fdb391d6f), ("f1e9fa064084d512", L6.Certs.Cf1e9fa064084d512), ("f6d365aab0daf77f", L6.Certs.Cf6d365aab0daf77f), ("fbfb6aade07413b6", L6.Certs.Cfbfb6aade07413b6), ("fc4b1268cbf99c5f", L6.Certs.Cfc4b1268cbf99c5f), ("fd4d5e4dd019e4eb", L6.Certs.Cfd4d5e4dd019e4eb)]
    7500 9000 { single := 397, core1 := 1103, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
