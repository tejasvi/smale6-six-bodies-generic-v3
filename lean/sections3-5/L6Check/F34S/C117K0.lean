import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C117
import L6Check.F34.Data.Common
import L6Check.F34.Data.C117
import L6Check.Certs.C6d21e7eccd073b25
import L6Check.Certs.C71745eaf4676f6fe

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 117, cells 0 ≤ cell < 2 of
`data/cells/c117.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 2` of class 117 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 2, core2 := 0, opn := 0 }. -/
theorem F34S_c117_k0 : checkChunkS 117 (L6.F2.diagOf 117) L6.F2.Data.cells_c117 single_117 links_117 pass_117 open43
    [("6d21e7eccd073b25", L6.Certs.C6d21e7eccd073b25), ("71745eaf4676f6fe", L6.Certs.C71745eaf4676f6fe)]
    0 2 { single := 0, core1 := 2, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
