import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C08b99e58e1acc2e1
import L6Check.Certs.C147b955ca1b11d54
import L6Check.Certs.C1e35066014af680f
import L6Check.Certs.C376b718487da742b
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C68a5a0f3bff515ac
import L6Check.Certs.C93549b380527c3e0
import L6Check.Certs.C9b5cd75375f980af
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cb0798c2bf2ea25ad
import L6Check.Certs.Cbb253f5966cad766
import L6Check.Certs.Cbf27248691902ac4
import L6Check.Certs.Cc283f4873b50bcb4
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cefbdadd3a9fafcff

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 25500 ≤ cell < 27000 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `25500 ≤ cell < 27000` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1150, core1 := 350, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k17 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("08b99e58e1acc2e1", L6.Certs.C08b99e58e1acc2e1), ("147b955ca1b11d54", L6.Certs.C147b955ca1b11d54), ("1e35066014af680f", L6.Certs.C1e35066014af680f), ("376b718487da742b", L6.Certs.C376b718487da742b), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("68a5a0f3bff515ac", L6.Certs.C68a5a0f3bff515ac), ("93549b380527c3e0", L6.Certs.C93549b380527c3e0), ("9b5cd75375f980af", L6.Certs.C9b5cd75375f980af), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("b0798c2bf2ea25ad", L6.Certs.Cb0798c2bf2ea25ad), ("bb253f5966cad766", L6.Certs.Cbb253f5966cad766), ("bf27248691902ac4", L6.Certs.Cbf27248691902ac4), ("c283f4873b50bcb4", L6.Certs.Cc283f4873b50bcb4), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("efbdadd3a9fafcff", L6.Certs.Cefbdadd3a9fafcff)]
    25500 27000 { single := 1150, core1 := 350, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
