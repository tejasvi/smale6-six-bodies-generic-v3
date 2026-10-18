import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C148
import L6Check.F34.Data.Common
import L6Check.F34.Data.C148
import L6Check.Certs.C0047d1cbcae52699
import L6Check.Certs.C0daf0f04f2c8251e
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1b3675cd0f814456
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C206108b4027e97cf
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C34adb611beeb99ee
import L6Check.Certs.C37e96d2833978eee
import L6Check.Certs.C386ed55a2ca8e7ec
import L6Check.Certs.C392aea6662b7eaef
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C53c8b2ddab2b632b
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C724a7accb412014a
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca852b6f1c1c7de3e
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cb1a8296b2bd2b206
import L6Check.Certs.Cb23daeafafb3e010
import L6Check.Certs.Cb5caef048fd37a47
import L6Check.Certs.Cbda63b1c3bf83f47
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cbf1c1072d313dea1
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc423f02ddcf0a15b
import L6Check.Certs.Ccd82dee8595a1e61
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce0c9beebe4ef485f
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Cec4b064f87dc1db8
import L6Check.Certs.Cefddd8b4a3c57d3d
import L6Check.Certs.Cf28b79cf11a54956
import L6Check.Certs.Cfc934afe0c2723c4

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 148, cells 1500 ≤ cell < 3000 of
`data/cells/c148.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `1500 ≤ cell < 3000` of class 148 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1223, core1 := 272, core2 := 5, opn := 0 }. -/
theorem F34S_c148_k1 : checkChunkS 148 (L6.F2.diagOf 148) L6.F2.Data.cells_c148 single_148 links_148 pass_148 open43
    [("0047d1cbcae52699", L6.Certs.C0047d1cbcae52699), ("0daf0f04f2c8251e", L6.Certs.C0daf0f04f2c8251e), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1b3675cd0f814456", L6.Certs.C1b3675cd0f814456), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("206108b4027e97cf", L6.Certs.C206108b4027e97cf), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("34adb611beeb99ee", L6.Certs.C34adb611beeb99ee), ("37e96d2833978eee", L6.Certs.C37e96d2833978eee), ("386ed55a2ca8e7ec", L6.Certs.C386ed55a2ca8e7ec), ("392aea6662b7eaef", L6.Certs.C392aea6662b7eaef), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("53c8b2ddab2b632b", L6.Certs.C53c8b2ddab2b632b), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("724a7accb412014a", L6.Certs.C724a7accb412014a), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a852b6f1c1c7de3e", L6.Certs.Ca852b6f1c1c7de3e), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("b1a8296b2bd2b206", L6.Certs.Cb1a8296b2bd2b206), ("b23daeafafb3e010", L6.Certs.Cb23daeafafb3e010), ("b5caef048fd37a47", L6.Certs.Cb5caef048fd37a47), ("bda63b1c3bf83f47", L6.Certs.Cbda63b1c3bf83f47), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("bf1c1072d313dea1", L6.Certs.Cbf1c1072d313dea1), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c423f02ddcf0a15b", L6.Certs.Cc423f02ddcf0a15b), ("cd82dee8595a1e61", L6.Certs.Ccd82dee8595a1e61), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e0c9beebe4ef485f", L6.Certs.Ce0c9beebe4ef485f), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("ec4b064f87dc1db8", L6.Certs.Cec4b064f87dc1db8), ("efddd8b4a3c57d3d", L6.Certs.Cefddd8b4a3c57d3d), ("f28b79cf11a54956", L6.Certs.Cf28b79cf11a54956), ("fc934afe0c2723c4", L6.Certs.Cfc934afe0c2723c4)]
    1500 3000 { single := 1223, core1 := 272, core2 := 5, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
