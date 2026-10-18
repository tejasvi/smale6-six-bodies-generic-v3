import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C1e35066014af680f
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C2d98fc5276cebdd8
import L6Check.Certs.C46bb7d1d47186aa8
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C57c2b2f3ce64f2cc
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.Ca697e155eadbb939
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Cb0798c2bf2ea25ad
import L6Check.Certs.Cb33ea2b4c1c341f9
import L6Check.Certs.Cb4ed27171c5a5f9f
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cdd4ee89766f77311

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 15000 ≤ cell < 16500 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `15000 ≤ cell < 16500` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1236, core1 := 264, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k10 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("1e35066014af680f", L6.Certs.C1e35066014af680f), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("2d98fc5276cebdd8", L6.Certs.C2d98fc5276cebdd8), ("46bb7d1d47186aa8", L6.Certs.C46bb7d1d47186aa8), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("57c2b2f3ce64f2cc", L6.Certs.C57c2b2f3ce64f2cc), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("a697e155eadbb939", L6.Certs.Ca697e155eadbb939), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("b0798c2bf2ea25ad", L6.Certs.Cb0798c2bf2ea25ad), ("b33ea2b4c1c341f9", L6.Certs.Cb33ea2b4c1c341f9), ("b4ed27171c5a5f9f", L6.Certs.Cb4ed27171c5a5f9f), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("dd4ee89766f77311", L6.Certs.Cdd4ee89766f77311)]
    15000 16500 { single := 1236, core1 := 264, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
