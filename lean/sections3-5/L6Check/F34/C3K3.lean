import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C072807f872160086
import L6Check.Certs.C1154f63f4ae46ba1
import L6Check.Certs.C152081021d735a63
import L6Check.Certs.C169462b19fb5aa18
import L6Check.Certs.C1a1f80a3e3602ed4
import L6Check.Certs.C1ebcaa9920466bde
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C22b24a11b523513b
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C2b1c0bd986785191
import L6Check.Certs.C32895f491bb8c754
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C4b429210c35ff1bb
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C67f91604077639fb
import L6Check.Certs.C6ab714f4d84692a6
import L6Check.Certs.C75077c3232d28783
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C85724ea81f29a188
import L6Check.Certs.C862e0c91863b7c35
import L6Check.Certs.C897da59625543f7b
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C90b15a7e7c4e4eb3
import L6Check.Certs.C9117280a7ad8e873
import L6Check.Certs.C99c63b41316cf3a6
import L6Check.Certs.C9a349c81467b57f5
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca05f78c08e847399
import L6Check.Certs.Ca561a929e7e499f5
import L6Check.Certs.Cae2ab36ffe129341
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Ccf7f7ca69feb518d
import L6Check.Certs.Cd4a904ae62aaaae5
import L6Check.Certs.Cdb6b3d87d1873df0
import L6Check.Certs.Cdd3879243137f416
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce14a1acf0eb39ff8
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce259d50945779b9d
import L6Check.Certs.Ce72b986f4c9e511e
import L6Check.Certs.Cec8dc5fe906620f8
import L6Check.Certs.Cecdc3c4e37764455
import L6Check.Certs.Ceead66d0c28971eb
import L6Check.Certs.Cf6344910dd62038d
import L6Check.Certs.Cfc95884a5bb38035

/-! F3/F4 (Proposition 5.3), class 3, cells 4500 ≤ cell < 6000 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `4500 ≤ cell < 6000` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 583, core1 := 917, core2 := 0, opn := 0 }. -/
theorem F34_c3_k3 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("072807f872160086", L6.Certs.C072807f872160086), ("1154f63f4ae46ba1", L6.Certs.C1154f63f4ae46ba1), ("152081021d735a63", L6.Certs.C152081021d735a63), ("169462b19fb5aa18", L6.Certs.C169462b19fb5aa18), ("1a1f80a3e3602ed4", L6.Certs.C1a1f80a3e3602ed4), ("1ebcaa9920466bde", L6.Certs.C1ebcaa9920466bde), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("22b24a11b523513b", L6.Certs.C22b24a11b523513b), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("2b1c0bd986785191", L6.Certs.C2b1c0bd986785191), ("32895f491bb8c754", L6.Certs.C32895f491bb8c754), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("4b429210c35ff1bb", L6.Certs.C4b429210c35ff1bb), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("67f91604077639fb", L6.Certs.C67f91604077639fb), ("6ab714f4d84692a6", L6.Certs.C6ab714f4d84692a6), ("75077c3232d28783", L6.Certs.C75077c3232d28783), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("85724ea81f29a188", L6.Certs.C85724ea81f29a188), ("862e0c91863b7c35", L6.Certs.C862e0c91863b7c35), ("897da59625543f7b", L6.Certs.C897da59625543f7b), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("90b15a7e7c4e4eb3", L6.Certs.C90b15a7e7c4e4eb3), ("9117280a7ad8e873", L6.Certs.C9117280a7ad8e873), ("99c63b41316cf3a6", L6.Certs.C99c63b41316cf3a6), ("9a349c81467b57f5", L6.Certs.C9a349c81467b57f5), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a05f78c08e847399", L6.Certs.Ca05f78c08e847399), ("a561a929e7e499f5", L6.Certs.Ca561a929e7e499f5), ("ae2ab36ffe129341", L6.Certs.Cae2ab36ffe129341), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("cf7f7ca69feb518d", L6.Certs.Ccf7f7ca69feb518d), ("d4a904ae62aaaae5", L6.Certs.Cd4a904ae62aaaae5), ("db6b3d87d1873df0", L6.Certs.Cdb6b3d87d1873df0), ("dd3879243137f416", L6.Certs.Cdd3879243137f416), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e14a1acf0eb39ff8", L6.Certs.Ce14a1acf0eb39ff8), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e259d50945779b9d", L6.Certs.Ce259d50945779b9d), ("e72b986f4c9e511e", L6.Certs.Ce72b986f4c9e511e), ("ec8dc5fe906620f8", L6.Certs.Cec8dc5fe906620f8), ("ecdc3c4e37764455", L6.Certs.Cecdc3c4e37764455), ("eead66d0c28971eb", L6.Certs.Ceead66d0c28971eb), ("f6344910dd62038d", L6.Certs.Cf6344910dd62038d), ("fc95884a5bb38035", L6.Certs.Cfc95884a5bb38035)]
    4500 6000 { single := 583, core1 := 917, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
