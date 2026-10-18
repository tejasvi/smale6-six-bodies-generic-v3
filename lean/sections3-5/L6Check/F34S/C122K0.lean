import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C122
import L6Check.F34.Data.Common
import L6Check.F34.Data.C122
import L6Check.Certs.C1eb593bc3c695606
import L6Check.Certs.C5353fad283bd1fe9
import L6Check.Certs.C5800c175b028cc82
import L6Check.Certs.C8857db9784f0fc0c
import L6Check.Certs.Cbc43a551b6dae1dc
import L6Check.Certs.Cdd820d8030a38f81

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 122, cells 0 ≤ cell < 10 of
`data/cells/c122.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 10` of class 122 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 10, core2 := 0, opn := 0 }. -/
theorem F34S_c122_k0 : checkChunkS 122 (L6.F2.diagOf 122) L6.F2.Data.cells_c122 single_122 links_122 pass_122 open43
    [("1eb593bc3c695606", L6.Certs.C1eb593bc3c695606), ("5353fad283bd1fe9", L6.Certs.C5353fad283bd1fe9), ("5800c175b028cc82", L6.Certs.C5800c175b028cc82), ("8857db9784f0fc0c", L6.Certs.C8857db9784f0fc0c), ("bc43a551b6dae1dc", L6.Certs.Cbc43a551b6dae1dc), ("dd820d8030a38f81", L6.Certs.Cdd820d8030a38f81)]
    0 10 { single := 0, core1 := 10, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
