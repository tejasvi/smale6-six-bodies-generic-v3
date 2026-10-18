import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C0726ad90b7fe118d
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C101a6627cf6fe849
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C26111d499f6cbb56
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C2d98fc5276cebdd8
import L6Check.Certs.C30184054f51d9e96
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C3f0a1164520df5d4
import L6Check.Certs.C46bb7d1d47186aa8
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C549547755e1f7a45
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C57c2b2f3ce64f2cc
import L6Check.Certs.C58744aa197893a83
import L6Check.Certs.C5c070f2fc555c352
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C6d7de0cc1be131cc
import L6Check.Certs.C6ff53cb44584c94d
import L6Check.Certs.C724a7accb412014a
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C98d57d5231d8f193
import L6Check.Certs.C99554a2fc1aa3180
import L6Check.Certs.C9afc567d75a8e62c
import L6Check.Certs.C9cf09299a811d19a
import L6Check.Certs.C9f7972664b835613
import L6Check.Certs.Ca0269f9ead157d0c
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca697e155eadbb939
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Cb33ea2b4c1c341f9
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Cb4b79584ea6a83a1
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cbf1c1072d313dea1
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cc51438b9ccf4edfb
import L6Check.Certs.Cd9a736f1204bda12
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cdd4ee89766f77311
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Ce80b80e4cb5ae9fe
import L6Check.Certs.Cea48080a5c1435fc
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Cf308512ed9e141fb
import L6Check.Certs.Cf75f12324fc8638c
import L6Check.Certs.Cf9e213c51db3acef

/-! F3/F4 (Proposition 5.3), class 128, cells 27000 ≤ cell < 28500 of `data/cells/c128.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `27000 ≤ cell < 28500` of class 128 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1091, core1 := 409, core2 := 0, opn := 0 }. -/
theorem F34_c128_k18 : checkChunk 128 n6 cells_128 single_128 links_128 pass_128 open43
    [("0726ad90b7fe118d", L6.Certs.C0726ad90b7fe118d), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("101a6627cf6fe849", L6.Certs.C101a6627cf6fe849), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("26111d499f6cbb56", L6.Certs.C26111d499f6cbb56), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("2d98fc5276cebdd8", L6.Certs.C2d98fc5276cebdd8), ("30184054f51d9e96", L6.Certs.C30184054f51d9e96), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("3f0a1164520df5d4", L6.Certs.C3f0a1164520df5d4), ("46bb7d1d47186aa8", L6.Certs.C46bb7d1d47186aa8), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("549547755e1f7a45", L6.Certs.C549547755e1f7a45), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("57c2b2f3ce64f2cc", L6.Certs.C57c2b2f3ce64f2cc), ("58744aa197893a83", L6.Certs.C58744aa197893a83), ("5c070f2fc555c352", L6.Certs.C5c070f2fc555c352), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("6d7de0cc1be131cc", L6.Certs.C6d7de0cc1be131cc), ("6ff53cb44584c94d", L6.Certs.C6ff53cb44584c94d), ("724a7accb412014a", L6.Certs.C724a7accb412014a), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("98d57d5231d8f193", L6.Certs.C98d57d5231d8f193), ("99554a2fc1aa3180", L6.Certs.C99554a2fc1aa3180), ("9afc567d75a8e62c", L6.Certs.C9afc567d75a8e62c), ("9cf09299a811d19a", L6.Certs.C9cf09299a811d19a), ("9f7972664b835613", L6.Certs.C9f7972664b835613), ("a0269f9ead157d0c", L6.Certs.Ca0269f9ead157d0c), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a697e155eadbb939", L6.Certs.Ca697e155eadbb939), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("b33ea2b4c1c341f9", L6.Certs.Cb33ea2b4c1c341f9), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("b4b79584ea6a83a1", L6.Certs.Cb4b79584ea6a83a1), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("bf1c1072d313dea1", L6.Certs.Cbf1c1072d313dea1), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("c51438b9ccf4edfb", L6.Certs.Cc51438b9ccf4edfb), ("d9a736f1204bda12", L6.Certs.Cd9a736f1204bda12), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("dd4ee89766f77311", L6.Certs.Cdd4ee89766f77311), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("e80b80e4cb5ae9fe", L6.Certs.Ce80b80e4cb5ae9fe), ("ea48080a5c1435fc", L6.Certs.Cea48080a5c1435fc), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("f308512ed9e141fb", L6.Certs.Cf308512ed9e141fb), ("f75f12324fc8638c", L6.Certs.Cf75f12324fc8638c), ("f9e213c51db3acef", L6.Certs.Cf9e213c51db3acef)]
    27000 28500 { single := 1091, core1 := 409, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
