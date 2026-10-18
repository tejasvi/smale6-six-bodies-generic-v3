import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C148
import L6Check.Certs.C0047d1cbcae52699
import L6Check.Certs.C0daf0f04f2c8251e
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C13ef8dbdd8bba9d7
import L6Check.Certs.C1614b3b557ef0fa6
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C206108b4027e97cf
import L6Check.Certs.C242c0a990a09d8e6
import L6Check.Certs.C25606d35193696e7
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C37e96d2833978eee
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C392aea6662b7eaef
import L6Check.Certs.C3d1de248748ce1ea
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C52cf87e3babff2d7
import L6Check.Certs.C53de25baa06ae77e
import L6Check.Certs.C53deb1e55eab591b
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C64e277638c43cdc4
import L6Check.Certs.C67f93868365353ac
import L6Check.Certs.C6e651153b41fa821
import L6Check.Certs.C75beaaf75ab02fdd
import L6Check.Certs.C7acdcbffc2a7e813
import L6Check.Certs.C7eed51cb14a8761d
import L6Check.Certs.C8078c84f6af4d144
import L6Check.Certs.C87646cfb8291a9c0
import L6Check.Certs.C8c096a307ea3e118
import L6Check.Certs.C8c6a426bb3dec47f
import L6Check.Certs.C8e0d296aa6245698
import L6Check.Certs.C90b5f3b832d0780c
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca852b6f1c1c7de3e
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cad402ea17c89cf5d
import L6Check.Certs.Cb1a8296b2bd2b206
import L6Check.Certs.Cb7111f680e9b2725
import L6Check.Certs.Cb8869a68e220593f
import L6Check.Certs.Cbc95f0a728d7d6c5
import L6Check.Certs.Cbda63b1c3bf83f47
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cc0b2acc0d217d09a
import L6Check.Certs.Cc0d47f3222e4d3a0
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc423f02ddcf0a15b
import L6Check.Certs.Cc9273cecc33f2aca
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cde5a0d2a57bac93c
import L6Check.Certs.Cde9e0c2d562c0d71
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Cefddd8b4a3c57d3d
import L6Check.Certs.Cf58b73d9b29a439a
import L6Check.Certs.Cf75f12324fc8638c

/-! F3/F4 (Proposition 5.3), class 148, cells 3000 ≤ cell < 4500 of `data/cells/c148.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `3000 ≤ cell < 4500` of class 148 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1233, core1 := 244, core2 := 23, opn := 0 }. -/
theorem F34_c148_k2 : checkChunk 148 n6 cells_148 single_148 links_148 pass_148 open43
    [("0047d1cbcae52699", L6.Certs.C0047d1cbcae52699), ("0daf0f04f2c8251e", L6.Certs.C0daf0f04f2c8251e), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("13ef8dbdd8bba9d7", L6.Certs.C13ef8dbdd8bba9d7), ("1614b3b557ef0fa6", L6.Certs.C1614b3b557ef0fa6), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("206108b4027e97cf", L6.Certs.C206108b4027e97cf), ("242c0a990a09d8e6", L6.Certs.C242c0a990a09d8e6), ("25606d35193696e7", L6.Certs.C25606d35193696e7), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("37e96d2833978eee", L6.Certs.C37e96d2833978eee), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("392aea6662b7eaef", L6.Certs.C392aea6662b7eaef), ("3d1de248748ce1ea", L6.Certs.C3d1de248748ce1ea), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("52cf87e3babff2d7", L6.Certs.C52cf87e3babff2d7), ("53de25baa06ae77e", L6.Certs.C53de25baa06ae77e), ("53deb1e55eab591b", L6.Certs.C53deb1e55eab591b), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("64e277638c43cdc4", L6.Certs.C64e277638c43cdc4), ("67f93868365353ac", L6.Certs.C67f93868365353ac), ("6e651153b41fa821", L6.Certs.C6e651153b41fa821), ("75beaaf75ab02fdd", L6.Certs.C75beaaf75ab02fdd), ("7acdcbffc2a7e813", L6.Certs.C7acdcbffc2a7e813), ("7eed51cb14a8761d", L6.Certs.C7eed51cb14a8761d), ("8078c84f6af4d144", L6.Certs.C8078c84f6af4d144), ("87646cfb8291a9c0", L6.Certs.C87646cfb8291a9c0), ("8c096a307ea3e118", L6.Certs.C8c096a307ea3e118), ("8c6a426bb3dec47f", L6.Certs.C8c6a426bb3dec47f), ("8e0d296aa6245698", L6.Certs.C8e0d296aa6245698), ("90b5f3b832d0780c", L6.Certs.C90b5f3b832d0780c), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a852b6f1c1c7de3e", L6.Certs.Ca852b6f1c1c7de3e), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("ad402ea17c89cf5d", L6.Certs.Cad402ea17c89cf5d), ("b1a8296b2bd2b206", L6.Certs.Cb1a8296b2bd2b206), ("b7111f680e9b2725", L6.Certs.Cb7111f680e9b2725), ("b8869a68e220593f", L6.Certs.Cb8869a68e220593f), ("bc95f0a728d7d6c5", L6.Certs.Cbc95f0a728d7d6c5), ("bda63b1c3bf83f47", L6.Certs.Cbda63b1c3bf83f47), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("c0b2acc0d217d09a", L6.Certs.Cc0b2acc0d217d09a), ("c0d47f3222e4d3a0", L6.Certs.Cc0d47f3222e4d3a0), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c423f02ddcf0a15b", L6.Certs.Cc423f02ddcf0a15b), ("c9273cecc33f2aca", L6.Certs.Cc9273cecc33f2aca), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("de5a0d2a57bac93c", L6.Certs.Cde5a0d2a57bac93c), ("de9e0c2d562c0d71", L6.Certs.Cde9e0c2d562c0d71), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("efddd8b4a3c57d3d", L6.Certs.Cefddd8b4a3c57d3d), ("f58b73d9b29a439a", L6.Certs.Cf58b73d9b29a439a), ("f75f12324fc8638c", L6.Certs.Cf75f12324fc8638c)]
    3000 4500 { single := 1233, core1 := 244, core2 := 23, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
