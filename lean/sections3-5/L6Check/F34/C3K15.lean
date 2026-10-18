import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C0b0e1e20c78f4361
import L6Check.Certs.C19998d415ed1923d
import L6Check.Certs.C1c96d2e008c11d60
import L6Check.Certs.C1f4dbbeb39e454c6
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C2232943207fcd89c
import L6Check.Certs.C24cfe809347b13ee
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C34060abcf4ebf91b
import L6Check.Certs.C3857f5902ffbc5a1
import L6Check.Certs.C391c3c7fc731914e
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.C496954832531bb6e
import L6Check.Certs.C4b059707de1e16cb
import L6Check.Certs.C4c382e1efbd3788a
import L6Check.Certs.C4f2d64643d1b7cf8
import L6Check.Certs.C5038acf7c79a60be
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5dbe42bc10c6f97b
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C642e0aeae4e4a71f
import L6Check.Certs.C665f3320a997b0ab
import L6Check.Certs.C6c5e96bff34ebc16
import L6Check.Certs.C6cb81b64dfa2ff3a
import L6Check.Certs.C75077c3232d28783
import L6Check.Certs.C7bb0ab61b0a0a34f
import L6Check.Certs.C7f10f1f3767082da
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C84252a07c5dde38c
import L6Check.Certs.C84ec4e3b1392a112
import L6Check.Certs.C8a58fb5ecae0a76c
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C90b15a7e7c4e4eb3
import L6Check.Certs.C91aa646ce133c185
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9b9bbf8a21ffc7e0
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca347ecdb0c926f85
import L6Check.Certs.Ca44a45eecd632d9c
import L6Check.Certs.Ca8a92faa68775195
import L6Check.Certs.Cae2ab36ffe129341
import L6Check.Certs.Cbee127c92fe6b2b9
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Cc61810f40c083e3b
import L6Check.Certs.Cd68770a84a659b4b
import L6Check.Certs.Cdd7d893c4f352770
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Cdfb1b2e94c6eef8c
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce36e575c21c81dd7
import L6Check.Certs.Cecc8f293e74a7d03
import L6Check.Certs.Ced1b37cf3216452a
import L6Check.Certs.Cf9d89ba1685be5ab

/-! F3/F4 (Proposition 5.3), class 3, cells 22500 ≤ cell < 24000 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `22500 ≤ cell < 24000` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 499, core1 := 1001, core2 := 0, opn := 0 }. -/
theorem F34_c3_k15 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("0b0e1e20c78f4361", L6.Certs.C0b0e1e20c78f4361), ("19998d415ed1923d", L6.Certs.C19998d415ed1923d), ("1c96d2e008c11d60", L6.Certs.C1c96d2e008c11d60), ("1f4dbbeb39e454c6", L6.Certs.C1f4dbbeb39e454c6), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("2232943207fcd89c", L6.Certs.C2232943207fcd89c), ("24cfe809347b13ee", L6.Certs.C24cfe809347b13ee), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("34060abcf4ebf91b", L6.Certs.C34060abcf4ebf91b), ("3857f5902ffbc5a1", L6.Certs.C3857f5902ffbc5a1), ("391c3c7fc731914e", L6.Certs.C391c3c7fc731914e), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("496954832531bb6e", L6.Certs.C496954832531bb6e), ("4b059707de1e16cb", L6.Certs.C4b059707de1e16cb), ("4c382e1efbd3788a", L6.Certs.C4c382e1efbd3788a), ("4f2d64643d1b7cf8", L6.Certs.C4f2d64643d1b7cf8), ("5038acf7c79a60be", L6.Certs.C5038acf7c79a60be), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5dbe42bc10c6f97b", L6.Certs.C5dbe42bc10c6f97b), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("642e0aeae4e4a71f", L6.Certs.C642e0aeae4e4a71f), ("665f3320a997b0ab", L6.Certs.C665f3320a997b0ab), ("6c5e96bff34ebc16", L6.Certs.C6c5e96bff34ebc16), ("6cb81b64dfa2ff3a", L6.Certs.C6cb81b64dfa2ff3a), ("75077c3232d28783", L6.Certs.C75077c3232d28783), ("7bb0ab61b0a0a34f", L6.Certs.C7bb0ab61b0a0a34f), ("7f10f1f3767082da", L6.Certs.C7f10f1f3767082da), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("84252a07c5dde38c", L6.Certs.C84252a07c5dde38c), ("84ec4e3b1392a112", L6.Certs.C84ec4e3b1392a112), ("8a58fb5ecae0a76c", L6.Certs.C8a58fb5ecae0a76c), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("90b15a7e7c4e4eb3", L6.Certs.C90b15a7e7c4e4eb3), ("91aa646ce133c185", L6.Certs.C91aa646ce133c185), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9b9bbf8a21ffc7e0", L6.Certs.C9b9bbf8a21ffc7e0), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a347ecdb0c926f85", L6.Certs.Ca347ecdb0c926f85), ("a44a45eecd632d9c", L6.Certs.Ca44a45eecd632d9c), ("a8a92faa68775195", L6.Certs.Ca8a92faa68775195), ("ae2ab36ffe129341", L6.Certs.Cae2ab36ffe129341), ("bee127c92fe6b2b9", L6.Certs.Cbee127c92fe6b2b9), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("c61810f40c083e3b", L6.Certs.Cc61810f40c083e3b), ("d68770a84a659b4b", L6.Certs.Cd68770a84a659b4b), ("dd7d893c4f352770", L6.Certs.Cdd7d893c4f352770), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("dfb1b2e94c6eef8c", L6.Certs.Cdfb1b2e94c6eef8c), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e36e575c21c81dd7", L6.Certs.Ce36e575c21c81dd7), ("ecc8f293e74a7d03", L6.Certs.Cecc8f293e74a7d03), ("ed1b37cf3216452a", L6.Certs.Ced1b37cf3216452a), ("f9d89ba1685be5ab", L6.Certs.Cf9d89ba1685be5ab)]
    22500 24000 { single := 499, core1 := 1001, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
