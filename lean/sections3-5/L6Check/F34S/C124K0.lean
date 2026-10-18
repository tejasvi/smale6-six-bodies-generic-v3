import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C124
import L6Check.F34.Data.Common
import L6Check.F34.Data.C124
import L6Check.Certs.C05b6fb1db9b2c00b
import L6Check.Certs.C13f31b33395992b0
import L6Check.Certs.C2069cc24c5c894a6
import L6Check.Certs.C305fe0a6e351ce93
import L6Check.Certs.C65669febace742ec
import L6Check.Certs.C780a1fce40bcc09a
import L6Check.Certs.Cc56d912715bfa614
import L6Check.Certs.Ce945b7556c943189

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 124, cells 0 ≤ cell < 143 of
`data/cells/c124.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 143` of class 124 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 132, core2 := 0, opn := 11 }. -/
theorem F34S_c124_k0 : checkChunkS 124 (L6.F2.diagOf 124) L6.F2.Data.cells_c124 single_124 links_124 pass_124 open43
    [("05b6fb1db9b2c00b", L6.Certs.C05b6fb1db9b2c00b), ("13f31b33395992b0", L6.Certs.C13f31b33395992b0), ("2069cc24c5c894a6", L6.Certs.C2069cc24c5c894a6), ("305fe0a6e351ce93", L6.Certs.C305fe0a6e351ce93), ("65669febace742ec", L6.Certs.C65669febace742ec), ("780a1fce40bcc09a", L6.Certs.C780a1fce40bcc09a), ("c56d912715bfa614", L6.Certs.Cc56d912715bfa614), ("e945b7556c943189", L6.Certs.Ce945b7556c943189)]
    0 143 { single := 0, core1 := 132, core2 := 0, opn := 11 } = true := by
  native_decide

end L6.F34S.Checks
