import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C3
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C049e29b443770507
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C0b0e1e20c78f4361
import L6Check.Certs.C1154f63f4ae46ba1
import L6Check.Certs.C1c96d2e008c11d60
import L6Check.Certs.C1f4dbbeb39e454c6
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C3082362f4383ae5f
import L6Check.Certs.C3857f5902ffbc5a1
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.C44d7aad63192c017
import L6Check.Certs.C496954832531bb6e
import L6Check.Certs.C4b059707de1e16cb
import L6Check.Certs.C4c382e1efbd3788a
import L6Check.Certs.C4f2d64643d1b7cf8
import L6Check.Certs.C5038acf7c79a60be
import L6Check.Certs.C5e3a9b185735ad11
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C642e0aeae4e4a71f
import L6Check.Certs.C6434a6f199774abf
import L6Check.Certs.C665f3320a997b0ab
import L6Check.Certs.C6ab714f4d84692a6
import L6Check.Certs.C6cb81b64dfa2ff3a
import L6Check.Certs.C75077c3232d28783
import L6Check.Certs.C7f10f1f3767082da
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C895c61d3288b6eef
import L6Check.Certs.C897da59625543f7b
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C91aa646ce133c185
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9b9bbf8a21ffc7e0
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca8a92faa68775195
import L6Check.Certs.Cbee127c92fe6b2b9
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc61810f40c083e3b
import L6Check.Certs.Cd68770a84a659b4b
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Cdfb1b2e94c6eef8c
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce259d50945779b9d
import L6Check.Certs.Ce36e575c21c81dd7
import L6Check.Certs.Cecc8f293e74a7d03
import L6Check.Certs.Cecdc3c4e37764455
import L6Check.Certs.Cef762e83bc6e8077
import L6Check.Certs.Cf6344910dd62038d
import L6Check.Certs.Cf9d89ba1685be5ab

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 3, cells 28500 ≤ cell < 30000 of
`data/cells/c3.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `28500 ≤ cell < 30000` of class 3 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1128, core1 := 372, core2 := 0, opn := 0 }. -/
theorem F34S_c3_k19 : checkChunkS 3 (L6.F2.diagOf 3) L6.F2.Data.cells_c3 single_3 links_3 pass_3 open43
    [("049e29b443770507", L6.Certs.C049e29b443770507), ("07018856a1764b34", L6.Certs.C07018856a1764b34), ("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("0b0e1e20c78f4361", L6.Certs.C0b0e1e20c78f4361), ("1154f63f4ae46ba1", L6.Certs.C1154f63f4ae46ba1), ("1c96d2e008c11d60", L6.Certs.C1c96d2e008c11d60), ("1f4dbbeb39e454c6", L6.Certs.C1f4dbbeb39e454c6), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("3082362f4383ae5f", L6.Certs.C3082362f4383ae5f), ("3857f5902ffbc5a1", L6.Certs.C3857f5902ffbc5a1), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("44d7aad63192c017", L6.Certs.C44d7aad63192c017), ("496954832531bb6e", L6.Certs.C496954832531bb6e), ("4b059707de1e16cb", L6.Certs.C4b059707de1e16cb), ("4c382e1efbd3788a", L6.Certs.C4c382e1efbd3788a), ("4f2d64643d1b7cf8", L6.Certs.C4f2d64643d1b7cf8), ("5038acf7c79a60be", L6.Certs.C5038acf7c79a60be), ("5e3a9b185735ad11", L6.Certs.C5e3a9b185735ad11), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("642e0aeae4e4a71f", L6.Certs.C642e0aeae4e4a71f), ("6434a6f199774abf", L6.Certs.C6434a6f199774abf), ("665f3320a997b0ab", L6.Certs.C665f3320a997b0ab), ("6ab714f4d84692a6", L6.Certs.C6ab714f4d84692a6), ("6cb81b64dfa2ff3a", L6.Certs.C6cb81b64dfa2ff3a), ("75077c3232d28783", L6.Certs.C75077c3232d28783), ("7f10f1f3767082da", L6.Certs.C7f10f1f3767082da), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("895c61d3288b6eef", L6.Certs.C895c61d3288b6eef), ("897da59625543f7b", L6.Certs.C897da59625543f7b), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("91aa646ce133c185", L6.Certs.C91aa646ce133c185), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9b9bbf8a21ffc7e0", L6.Certs.C9b9bbf8a21ffc7e0), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a8a92faa68775195", L6.Certs.Ca8a92faa68775195), ("bee127c92fe6b2b9", L6.Certs.Cbee127c92fe6b2b9), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c61810f40c083e3b", L6.Certs.Cc61810f40c083e3b), ("d68770a84a659b4b", L6.Certs.Cd68770a84a659b4b), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("dfb1b2e94c6eef8c", L6.Certs.Cdfb1b2e94c6eef8c), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e259d50945779b9d", L6.Certs.Ce259d50945779b9d), ("e36e575c21c81dd7", L6.Certs.Ce36e575c21c81dd7), ("ecc8f293e74a7d03", L6.Certs.Cecc8f293e74a7d03), ("ecdc3c4e37764455", L6.Certs.Cecdc3c4e37764455), ("ef762e83bc6e8077", L6.Certs.Cef762e83bc6e8077), ("f6344910dd62038d", L6.Certs.Cf6344910dd62038d), ("f9d89ba1685be5ab", L6.Certs.Cf9d89ba1685be5ab)]
    28500 30000 { single := 1128, core1 := 372, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
