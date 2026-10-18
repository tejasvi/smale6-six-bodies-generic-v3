import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C0
import L6Check.F34.Data.Common
import L6Check.F34.Data.C0
import L6Check.Certs.C6d070a436b17b685
import L6Check.Certs.C9b64464954a9e18b
import L6Check.Certs.Ca7e0897348bf27b5
import L6Check.Certs.Cac0f809f802be745
import L6Check.Certs.Cc5bd52e00bd7db78
import L6Check.Certs.Cea429f93ce228be4
import L6Check.Certs.Cfe9c1a05c0c02e21

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 0, cells 0 ≤ cell < 17 of
`data/cells/c0.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 17` of class 0 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 8, core1 := 9, core2 := 0, opn := 0 }. -/
theorem F34S_c0_k0 : checkChunkS 0 (L6.F2.diagOf 0) L6.F2.Data.cells_c0 single_0 links_0 pass_0 open43
    [("6d070a436b17b685", L6.Certs.C6d070a436b17b685), ("9b64464954a9e18b", L6.Certs.C9b64464954a9e18b), ("a7e0897348bf27b5", L6.Certs.Ca7e0897348bf27b5), ("ac0f809f802be745", L6.Certs.Cac0f809f802be745), ("c5bd52e00bd7db78", L6.Certs.Cc5bd52e00bd7db78), ("ea429f93ce228be4", L6.Certs.Cea429f93ce228be4), ("fe9c1a05c0c02e21", L6.Certs.Cfe9c1a05c0c02e21)]
    0 17 { single := 8, core1 := 9, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
