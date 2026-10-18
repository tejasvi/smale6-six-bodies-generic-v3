import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C09160743fb63ece9
import L6Check.Certs.C14388f47e4573dd4
import L6Check.Certs.C1c96d2e008c11d60
import L6Check.Certs.C1f4dbbeb39e454c6
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C3857f5902ffbc5a1
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C44d7aad63192c017
import L6Check.Certs.C496954832531bb6e
import L6Check.Certs.C4b059707de1e16cb
import L6Check.Certs.C4c382e1efbd3788a
import L6Check.Certs.C4f2d64643d1b7cf8
import L6Check.Certs.C5038acf7c79a60be
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5a12e6ae2f834977
import L6Check.Certs.C5c2dbdb33b3b95d4
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C665f3320a997b0ab
import L6Check.Certs.C6dc98f1e972d33c8
import L6Check.Certs.C75077c3232d28783
import L6Check.Certs.C78a98147aa1211a5
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C895c61d3288b6eef
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9b9bbf8a21ffc7e0
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca8a92faa68775195
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Cd225792bede077bc
import L6Check.Certs.Cd8deb7b57e227fe5
import L6Check.Certs.Cd9ad20a9ad3ca819
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce36e575c21c81dd7
import L6Check.Certs.Cf9d89ba1685be5ab

/-! F3/F4 (Proposition 5.3), class 3, cells 34500 ≤ cell < 36000 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `34500 ≤ cell < 36000` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 537, core1 := 963, core2 := 0, opn := 0 }. -/
theorem F34_c3_k23 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("09160743fb63ece9", L6.Certs.C09160743fb63ece9), ("14388f47e4573dd4", L6.Certs.C14388f47e4573dd4), ("1c96d2e008c11d60", L6.Certs.C1c96d2e008c11d60), ("1f4dbbeb39e454c6", L6.Certs.C1f4dbbeb39e454c6), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("3857f5902ffbc5a1", L6.Certs.C3857f5902ffbc5a1), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("44d7aad63192c017", L6.Certs.C44d7aad63192c017), ("496954832531bb6e", L6.Certs.C496954832531bb6e), ("4b059707de1e16cb", L6.Certs.C4b059707de1e16cb), ("4c382e1efbd3788a", L6.Certs.C4c382e1efbd3788a), ("4f2d64643d1b7cf8", L6.Certs.C4f2d64643d1b7cf8), ("5038acf7c79a60be", L6.Certs.C5038acf7c79a60be), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5a12e6ae2f834977", L6.Certs.C5a12e6ae2f834977), ("5c2dbdb33b3b95d4", L6.Certs.C5c2dbdb33b3b95d4), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("665f3320a997b0ab", L6.Certs.C665f3320a997b0ab), ("6dc98f1e972d33c8", L6.Certs.C6dc98f1e972d33c8), ("75077c3232d28783", L6.Certs.C75077c3232d28783), ("78a98147aa1211a5", L6.Certs.C78a98147aa1211a5), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("895c61d3288b6eef", L6.Certs.C895c61d3288b6eef), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9b9bbf8a21ffc7e0", L6.Certs.C9b9bbf8a21ffc7e0), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a8a92faa68775195", L6.Certs.Ca8a92faa68775195), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("d225792bede077bc", L6.Certs.Cd225792bede077bc), ("d8deb7b57e227fe5", L6.Certs.Cd8deb7b57e227fe5), ("d9ad20a9ad3ca819", L6.Certs.Cd9ad20a9ad3ca819), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e36e575c21c81dd7", L6.Certs.Ce36e575c21c81dd7), ("f9d89ba1685be5ab", L6.Certs.Cf9d89ba1685be5ab)]
    34500 36000 { single := 537, core1 := 963, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
