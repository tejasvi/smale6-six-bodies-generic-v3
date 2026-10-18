import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C147b955ca1b11d54
import L6Check.Certs.C206108b4027e97cf
import L6Check.Certs.C2d98fc5276cebdd8
import L6Check.Certs.C376b718487da742b
import L6Check.Certs.C46bb7d1d47186aa8
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C57c2b2f3ce64f2cc
import L6Check.Certs.C60742c0aa412da86
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C68a5a0f3bff515ac
import L6Check.Certs.C7972111a1147fdc1
import L6Check.Certs.C9b5cd75375f980af
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca697e155eadbb939
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cb33ea2b4c1c341f9
import L6Check.Certs.Cbb253f5966cad766
import L6Check.Certs.Cbf1c1072d313dea1
import L6Check.Certs.Cbf27248691902ac4
import L6Check.Certs.Cc283f4873b50bcb4
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cdd4ee89766f77311
import L6Check.Certs.Cefbdadd3a9fafcff
import L6Check.Certs.Cf9e213c51db3acef
import L6Check.Certs.Cfb26a2f26815b2d8

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 16500 ≤ cell < 18000 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `16500 ≤ cell < 18000` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1094, core1 := 406, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k11 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("147b955ca1b11d54", L6.Certs.C147b955ca1b11d54), ("206108b4027e97cf", L6.Certs.C206108b4027e97cf), ("2d98fc5276cebdd8", L6.Certs.C2d98fc5276cebdd8), ("376b718487da742b", L6.Certs.C376b718487da742b), ("46bb7d1d47186aa8", L6.Certs.C46bb7d1d47186aa8), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("57c2b2f3ce64f2cc", L6.Certs.C57c2b2f3ce64f2cc), ("60742c0aa412da86", L6.Certs.C60742c0aa412da86), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("68a5a0f3bff515ac", L6.Certs.C68a5a0f3bff515ac), ("7972111a1147fdc1", L6.Certs.C7972111a1147fdc1), ("9b5cd75375f980af", L6.Certs.C9b5cd75375f980af), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a697e155eadbb939", L6.Certs.Ca697e155eadbb939), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("b33ea2b4c1c341f9", L6.Certs.Cb33ea2b4c1c341f9), ("bb253f5966cad766", L6.Certs.Cbb253f5966cad766), ("bf1c1072d313dea1", L6.Certs.Cbf1c1072d313dea1), ("bf27248691902ac4", L6.Certs.Cbf27248691902ac4), ("c283f4873b50bcb4", L6.Certs.Cc283f4873b50bcb4), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("dd4ee89766f77311", L6.Certs.Cdd4ee89766f77311), ("efbdadd3a9fafcff", L6.Certs.Cefbdadd3a9fafcff), ("f9e213c51db3acef", L6.Certs.Cf9e213c51db3acef), ("fb26a2f26815b2d8", L6.Certs.Cfb26a2f26815b2d8)]
    16500 18000 { single := 1094, core1 := 406, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
