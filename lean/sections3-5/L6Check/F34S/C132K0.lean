import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C132
import L6Check.F34.Data.Common
import L6Check.F34.Data.C132
import L6Check.Certs.C085a33b7d1d675c9
import L6Check.Certs.C4182694dbabca56f
import L6Check.Certs.C4e77f5f512983c9f
import L6Check.Certs.C591dad9a9e121435
import L6Check.Certs.C661441e082bf5fdc
import L6Check.Certs.C7a98202209d08e42
import L6Check.Certs.Cbce719b84d6df6d2
import L6Check.Certs.Cd30bf77ee6877a5c
import L6Check.Certs.Ce15e707b5b269e6d
import L6Check.Certs.Cf0cccaca3ee113dc
import L6Check.Certs.Cffa2ee29f5ac013e

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 132, cells 0 ≤ cell < 147 of
`data/cells/c132.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 147` of class 132 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 145, core2 := 1, opn := 1 }. -/
theorem F34S_c132_k0 : checkChunkS 132 (L6.F2.diagOf 132) L6.F2.Data.cells_c132 single_132 links_132 pass_132 open43
    [("085a33b7d1d675c9", L6.Certs.C085a33b7d1d675c9), ("4182694dbabca56f", L6.Certs.C4182694dbabca56f), ("4e77f5f512983c9f", L6.Certs.C4e77f5f512983c9f), ("591dad9a9e121435", L6.Certs.C591dad9a9e121435), ("661441e082bf5fdc", L6.Certs.C661441e082bf5fdc), ("7a98202209d08e42", L6.Certs.C7a98202209d08e42), ("bce719b84d6df6d2", L6.Certs.Cbce719b84d6df6d2), ("d30bf77ee6877a5c", L6.Certs.Cd30bf77ee6877a5c), ("e15e707b5b269e6d", L6.Certs.Ce15e707b5b269e6d), ("f0cccaca3ee113dc", L6.Certs.Cf0cccaca3ee113dc), ("ffa2ee29f5ac013e", L6.Certs.Cffa2ee29f5ac013e)]
    0 147 { single := 0, core1 := 145, core2 := 1, opn := 1 } = true := by
  native_decide

end L6.F34S.Checks
