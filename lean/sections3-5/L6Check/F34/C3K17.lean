import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C072807f872160086
import L6Check.Certs.C09160743fb63ece9
import L6Check.Certs.C169462b19fb5aa18
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C2b1c0bd986785191
import L6Check.Certs.C32895f491bb8c754
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C44d7aad63192c017
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5c2dbdb33b3b95d4
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C67f91604077639fb
import L6Check.Certs.C6ab714f4d84692a6
import L6Check.Certs.C75077c3232d28783
import L6Check.Certs.C78a98147aa1211a5
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C897da59625543f7b
import L6Check.Certs.C8a8322f07e50e771
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C9117280a7ad8e873
import L6Check.Certs.C99c63b41316cf3a6
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca561a929e7e499f5
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Cc8ef113f686cf0c4
import L6Check.Certs.Ccf7f7ca69feb518d
import L6Check.Certs.Cd8deb7b57e227fe5
import L6Check.Certs.Cd9ad20a9ad3ca819
import L6Check.Certs.Cdb6b3d87d1873df0
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce259d50945779b9d
import L6Check.Certs.Cecdc3c4e37764455
import L6Check.Certs.Ceead66d0c28971eb
import L6Check.Certs.Cef762e83bc6e8077
import L6Check.Certs.Cf6344910dd62038d

/-! F3/F4 (Proposition 5.3), class 3, cells 25500 ≤ cell < 27000 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `25500 ≤ cell < 27000` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 573, core1 := 927, core2 := 0, opn := 0 }. -/
theorem F34_c3_k17 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("072807f872160086", L6.Certs.C072807f872160086), ("09160743fb63ece9", L6.Certs.C09160743fb63ece9), ("169462b19fb5aa18", L6.Certs.C169462b19fb5aa18), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("2b1c0bd986785191", L6.Certs.C2b1c0bd986785191), ("32895f491bb8c754", L6.Certs.C32895f491bb8c754), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("44d7aad63192c017", L6.Certs.C44d7aad63192c017), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5c2dbdb33b3b95d4", L6.Certs.C5c2dbdb33b3b95d4), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("67f91604077639fb", L6.Certs.C67f91604077639fb), ("6ab714f4d84692a6", L6.Certs.C6ab714f4d84692a6), ("75077c3232d28783", L6.Certs.C75077c3232d28783), ("78a98147aa1211a5", L6.Certs.C78a98147aa1211a5), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("897da59625543f7b", L6.Certs.C897da59625543f7b), ("8a8322f07e50e771", L6.Certs.C8a8322f07e50e771), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("9117280a7ad8e873", L6.Certs.C9117280a7ad8e873), ("99c63b41316cf3a6", L6.Certs.C99c63b41316cf3a6), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a561a929e7e499f5", L6.Certs.Ca561a929e7e499f5), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("c8ef113f686cf0c4", L6.Certs.Cc8ef113f686cf0c4), ("cf7f7ca69feb518d", L6.Certs.Ccf7f7ca69feb518d), ("d8deb7b57e227fe5", L6.Certs.Cd8deb7b57e227fe5), ("d9ad20a9ad3ca819", L6.Certs.Cd9ad20a9ad3ca819), ("db6b3d87d1873df0", L6.Certs.Cdb6b3d87d1873df0), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e259d50945779b9d", L6.Certs.Ce259d50945779b9d), ("ecdc3c4e37764455", L6.Certs.Cecdc3c4e37764455), ("eead66d0c28971eb", L6.Certs.Ceead66d0c28971eb), ("ef762e83bc6e8077", L6.Certs.Cef762e83bc6e8077), ("f6344910dd62038d", L6.Certs.Cf6344910dd62038d)]
    25500 27000 { single := 573, core1 := 927, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
