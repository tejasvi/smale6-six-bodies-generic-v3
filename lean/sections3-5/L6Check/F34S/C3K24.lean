import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C3
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C0b0e1e20c78f4361
import L6Check.Certs.C19998d415ed1923d
import L6Check.Certs.C1f4dbbeb39e454c6
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C2232943207fcd89c
import L6Check.Certs.C24cfe809347b13ee
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C2e575f1e789025b4
import L6Check.Certs.C3058c17cac9a07d0
import L6Check.Certs.C35f1da0b6e4adebb
import L6Check.Certs.C3857f5902ffbc5a1
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C449a597596e67f40
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.C496954832531bb6e
import L6Check.Certs.C4f2d64643d1b7cf8
import L6Check.Certs.C5038acf7c79a60be
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5b4e2cd632e36834
import L6Check.Certs.C5c2dbdb33b3b95d4
import L6Check.Certs.C5dbe42bc10c6f97b
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C642e0aeae4e4a71f
import L6Check.Certs.C665f3320a997b0ab
import L6Check.Certs.C6cb81b64dfa2ff3a
import L6Check.Certs.C6dc98f1e972d33c8
import L6Check.Certs.C7bb0ab61b0a0a34f
import L6Check.Certs.C7f10f1f3767082da
import L6Check.Certs.C8351297e112bdabc
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C84252a07c5dde38c
import L6Check.Certs.C84ec4e3b1392a112
import L6Check.Certs.C895c61d3288b6eef
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C91aa646ce133c185
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9b9bbf8a21ffc7e0
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca347ecdb0c926f85
import L6Check.Certs.Ca44a45eecd632d9c
import L6Check.Certs.Ca8a92faa68775195
import L6Check.Certs.Cbee127c92fe6b2b9
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Cc61810f40c083e3b
import L6Check.Certs.Ccb8bd9135274f22b
import L6Check.Certs.Cd68770a84a659b4b
import L6Check.Certs.Cd8deb7b57e227fe5
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce36e575c21c81dd7
import L6Check.Certs.Cecc8f293e74a7d03
import L6Check.Certs.Cf9d89ba1685be5ab

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 3, cells 36000 ≤ cell < 37500 of
`data/cells/c3.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `36000 ≤ cell < 37500` of class 3 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 757, core1 := 743, core2 := 0, opn := 0 }. -/
theorem F34S_c3_k24 : checkChunkS 3 (L6.F2.diagOf 3) L6.F2.Data.cells_c3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("0b0e1e20c78f4361", L6.Certs.C0b0e1e20c78f4361), ("19998d415ed1923d", L6.Certs.C19998d415ed1923d), ("1f4dbbeb39e454c6", L6.Certs.C1f4dbbeb39e454c6), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("2232943207fcd89c", L6.Certs.C2232943207fcd89c), ("24cfe809347b13ee", L6.Certs.C24cfe809347b13ee), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("2e575f1e789025b4", L6.Certs.C2e575f1e789025b4), ("3058c17cac9a07d0", L6.Certs.C3058c17cac9a07d0), ("35f1da0b6e4adebb", L6.Certs.C35f1da0b6e4adebb), ("3857f5902ffbc5a1", L6.Certs.C3857f5902ffbc5a1), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("449a597596e67f40", L6.Certs.C449a597596e67f40), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("496954832531bb6e", L6.Certs.C496954832531bb6e), ("4f2d64643d1b7cf8", L6.Certs.C4f2d64643d1b7cf8), ("5038acf7c79a60be", L6.Certs.C5038acf7c79a60be), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5b4e2cd632e36834", L6.Certs.C5b4e2cd632e36834), ("5c2dbdb33b3b95d4", L6.Certs.C5c2dbdb33b3b95d4), ("5dbe42bc10c6f97b", L6.Certs.C5dbe42bc10c6f97b), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("642e0aeae4e4a71f", L6.Certs.C642e0aeae4e4a71f), ("665f3320a997b0ab", L6.Certs.C665f3320a997b0ab), ("6cb81b64dfa2ff3a", L6.Certs.C6cb81b64dfa2ff3a), ("6dc98f1e972d33c8", L6.Certs.C6dc98f1e972d33c8), ("7bb0ab61b0a0a34f", L6.Certs.C7bb0ab61b0a0a34f), ("7f10f1f3767082da", L6.Certs.C7f10f1f3767082da), ("8351297e112bdabc", L6.Certs.C8351297e112bdabc), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("84252a07c5dde38c", L6.Certs.C84252a07c5dde38c), ("84ec4e3b1392a112", L6.Certs.C84ec4e3b1392a112), ("895c61d3288b6eef", L6.Certs.C895c61d3288b6eef), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("91aa646ce133c185", L6.Certs.C91aa646ce133c185), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9b9bbf8a21ffc7e0", L6.Certs.C9b9bbf8a21ffc7e0), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a347ecdb0c926f85", L6.Certs.Ca347ecdb0c926f85), ("a44a45eecd632d9c", L6.Certs.Ca44a45eecd632d9c), ("a8a92faa68775195", L6.Certs.Ca8a92faa68775195), ("bee127c92fe6b2b9", L6.Certs.Cbee127c92fe6b2b9), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("c61810f40c083e3b", L6.Certs.Cc61810f40c083e3b), ("cb8bd9135274f22b", L6.Certs.Ccb8bd9135274f22b), ("d68770a84a659b4b", L6.Certs.Cd68770a84a659b4b), ("d8deb7b57e227fe5", L6.Certs.Cd8deb7b57e227fe5), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e36e575c21c81dd7", L6.Certs.Ce36e575c21c81dd7), ("ecc8f293e74a7d03", L6.Certs.Cecc8f293e74a7d03), ("f9d89ba1685be5ab", L6.Certs.Cf9d89ba1685be5ab)]
    36000 37500 { single := 757, core1 := 743, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
