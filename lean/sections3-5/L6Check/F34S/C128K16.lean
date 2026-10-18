import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C147b955ca1b11d54
import L6Check.Certs.C1e35066014af680f
import L6Check.Certs.C206108b4027e97cf
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C376b718487da742b
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C5a94e6f179d11010
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C60742c0aa412da86
import L6Check.Certs.C68a5a0f3bff515ac
import L6Check.Certs.C7972111a1147fdc1
import L6Check.Certs.C9b5cd75375f980af
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Cbf27248691902ac4
import L6Check.Certs.Cc283f4873b50bcb4
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Cefbdadd3a9fafcff
import L6Check.Certs.Cfb26a2f26815b2d8

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 24000 ≤ cell < 25500 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `24000 ≤ cell < 25500` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1267, core1 := 233, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k16 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("147b955ca1b11d54", L6.Certs.C147b955ca1b11d54), ("1e35066014af680f", L6.Certs.C1e35066014af680f), ("206108b4027e97cf", L6.Certs.C206108b4027e97cf), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("376b718487da742b", L6.Certs.C376b718487da742b), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("5a94e6f179d11010", L6.Certs.C5a94e6f179d11010), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("60742c0aa412da86", L6.Certs.C60742c0aa412da86), ("68a5a0f3bff515ac", L6.Certs.C68a5a0f3bff515ac), ("7972111a1147fdc1", L6.Certs.C7972111a1147fdc1), ("9b5cd75375f980af", L6.Certs.C9b5cd75375f980af), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("bf27248691902ac4", L6.Certs.Cbf27248691902ac4), ("c283f4873b50bcb4", L6.Certs.Cc283f4873b50bcb4), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("efbdadd3a9fafcff", L6.Certs.Cefbdadd3a9fafcff), ("fb26a2f26815b2d8", L6.Certs.Cfb26a2f26815b2d8)]
    24000 25500 { single := 1267, core1 := 233, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
