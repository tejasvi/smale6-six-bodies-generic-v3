import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C147b955ca1b11d54
import L6Check.Certs.C16c607738140b7f4
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C260dc626db027e9c
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C2d98fc5276cebdd8
import L6Check.Certs.C376b718487da742b
import L6Check.Certs.C46bb7d1d47186aa8
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C57c2b2f3ce64f2cc
import L6Check.Certs.C5d23d8880d91e302
import L6Check.Certs.C60742c0aa412da86
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C6ff53cb44584c94d
import L6Check.Certs.C7972111a1147fdc1
import L6Check.Certs.C879fb5d82e0a8167
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C93549b380527c3e0
import L6Check.Certs.C9994472ee3a3df0a
import L6Check.Certs.C9b5cd75375f980af
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca697e155eadbb939
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cb33ea2b4c1c341f9
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Cbb253f5966cad766
import L6Check.Certs.Cbf1c1072d313dea1
import L6Check.Certs.Cbf27248691902ac4
import L6Check.Certs.Cc283f4873b50bcb4
import L6Check.Certs.Ccf20072e83aaa6fb
import L6Check.Certs.Cd363b7180a66c9b5
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cdc8b9573655396e4
import L6Check.Certs.Cdd4ee89766f77311
import L6Check.Certs.Ce11b7354ea07bda3
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Cefbdadd3a9fafcff
import L6Check.Certs.Cf9e213c51db3acef
import L6Check.Certs.Cfb26a2f26815b2d8

/-! F3/F4 (Proposition 5.3), class 128, cells 3000 ≤ cell < 4500 of `data/cells/c128.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `3000 ≤ cell < 4500` of class 128 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1020, core1 := 480, core2 := 0, opn := 0 }. -/
theorem F34_c128_k2 : checkChunk 128 n6 cells_128 single_128 links_128 pass_128 open43
    [("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("147b955ca1b11d54", L6.Certs.C147b955ca1b11d54), ("16c607738140b7f4", L6.Certs.C16c607738140b7f4), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("260dc626db027e9c", L6.Certs.C260dc626db027e9c), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("2d98fc5276cebdd8", L6.Certs.C2d98fc5276cebdd8), ("376b718487da742b", L6.Certs.C376b718487da742b), ("46bb7d1d47186aa8", L6.Certs.C46bb7d1d47186aa8), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("57c2b2f3ce64f2cc", L6.Certs.C57c2b2f3ce64f2cc), ("5d23d8880d91e302", L6.Certs.C5d23d8880d91e302), ("60742c0aa412da86", L6.Certs.C60742c0aa412da86), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("6ff53cb44584c94d", L6.Certs.C6ff53cb44584c94d), ("7972111a1147fdc1", L6.Certs.C7972111a1147fdc1), ("879fb5d82e0a8167", L6.Certs.C879fb5d82e0a8167), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("93549b380527c3e0", L6.Certs.C93549b380527c3e0), ("9994472ee3a3df0a", L6.Certs.C9994472ee3a3df0a), ("9b5cd75375f980af", L6.Certs.C9b5cd75375f980af), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a697e155eadbb939", L6.Certs.Ca697e155eadbb939), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("b33ea2b4c1c341f9", L6.Certs.Cb33ea2b4c1c341f9), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("bb253f5966cad766", L6.Certs.Cbb253f5966cad766), ("bf1c1072d313dea1", L6.Certs.Cbf1c1072d313dea1), ("bf27248691902ac4", L6.Certs.Cbf27248691902ac4), ("c283f4873b50bcb4", L6.Certs.Cc283f4873b50bcb4), ("cf20072e83aaa6fb", L6.Certs.Ccf20072e83aaa6fb), ("d363b7180a66c9b5", L6.Certs.Cd363b7180a66c9b5), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("dc8b9573655396e4", L6.Certs.Cdc8b9573655396e4), ("dd4ee89766f77311", L6.Certs.Cdd4ee89766f77311), ("e11b7354ea07bda3", L6.Certs.Ce11b7354ea07bda3), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("efbdadd3a9fafcff", L6.Certs.Cefbdadd3a9fafcff), ("f9e213c51db3acef", L6.Certs.Cf9e213c51db3acef), ("fb26a2f26815b2d8", L6.Certs.Cfb26a2f26815b2d8)]
    3000 4500 { single := 1020, core1 := 480, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
