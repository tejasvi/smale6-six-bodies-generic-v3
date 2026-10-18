import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C0870e0cd7eb675aa
import L6Check.Certs.C09160743fb63ece9
import L6Check.Certs.C1154f63f4ae46ba1
import L6Check.Certs.C152081021d735a63
import L6Check.Certs.C169462b19fb5aa18
import L6Check.Certs.C1a1f80a3e3602ed4
import L6Check.Certs.C1ebcaa9920466bde
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C22b24a11b523513b
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C3058c17cac9a07d0
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C449a597596e67f40
import L6Check.Certs.C44d7aad63192c017
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C599e1faa03f611df
import L6Check.Certs.C60a265d390177e9e
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C67f91604077639fb
import L6Check.Certs.C6ab714f4d84692a6
import L6Check.Certs.C8351297e112bdabc
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C85724ea81f29a188
import L6Check.Certs.C862e0c91863b7c35
import L6Check.Certs.C897da59625543f7b
import L6Check.Certs.C8a8322f07e50e771
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C969ffce4b44b666b
import L6Check.Certs.C99c63b41316cf3a6
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca561a929e7e499f5
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Ccf7f7ca69feb518d
import L6Check.Certs.Cd4a904ae62aaaae5
import L6Check.Certs.Cdb6b3d87d1873df0
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce14a1acf0eb39ff8
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce259d50945779b9d
import L6Check.Certs.Ce72b986f4c9e511e
import L6Check.Certs.Cecdc3c4e37764455
import L6Check.Certs.Ceead66d0c28971eb
import L6Check.Certs.Cef762e83bc6e8077
import L6Check.Certs.Cf6344910dd62038d
import L6Check.Certs.Cfc95884a5bb38035

/-! F3/F4 (Proposition 5.3), class 3, cells 27000 ≤ cell < 28500 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `27000 ≤ cell < 28500` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 729, core1 := 771, core2 := 0, opn := 0 }. -/
theorem F34_c3_k18 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("0870e0cd7eb675aa", L6.Certs.C0870e0cd7eb675aa), ("09160743fb63ece9", L6.Certs.C09160743fb63ece9), ("1154f63f4ae46ba1", L6.Certs.C1154f63f4ae46ba1), ("152081021d735a63", L6.Certs.C152081021d735a63), ("169462b19fb5aa18", L6.Certs.C169462b19fb5aa18), ("1a1f80a3e3602ed4", L6.Certs.C1a1f80a3e3602ed4), ("1ebcaa9920466bde", L6.Certs.C1ebcaa9920466bde), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("22b24a11b523513b", L6.Certs.C22b24a11b523513b), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("3058c17cac9a07d0", L6.Certs.C3058c17cac9a07d0), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("449a597596e67f40", L6.Certs.C449a597596e67f40), ("44d7aad63192c017", L6.Certs.C44d7aad63192c017), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("599e1faa03f611df", L6.Certs.C599e1faa03f611df), ("60a265d390177e9e", L6.Certs.C60a265d390177e9e), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("67f91604077639fb", L6.Certs.C67f91604077639fb), ("6ab714f4d84692a6", L6.Certs.C6ab714f4d84692a6), ("8351297e112bdabc", L6.Certs.C8351297e112bdabc), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("85724ea81f29a188", L6.Certs.C85724ea81f29a188), ("862e0c91863b7c35", L6.Certs.C862e0c91863b7c35), ("897da59625543f7b", L6.Certs.C897da59625543f7b), ("8a8322f07e50e771", L6.Certs.C8a8322f07e50e771), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("969ffce4b44b666b", L6.Certs.C969ffce4b44b666b), ("99c63b41316cf3a6", L6.Certs.C99c63b41316cf3a6), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a561a929e7e499f5", L6.Certs.Ca561a929e7e499f5), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("cf7f7ca69feb518d", L6.Certs.Ccf7f7ca69feb518d), ("d4a904ae62aaaae5", L6.Certs.Cd4a904ae62aaaae5), ("db6b3d87d1873df0", L6.Certs.Cdb6b3d87d1873df0), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e14a1acf0eb39ff8", L6.Certs.Ce14a1acf0eb39ff8), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e259d50945779b9d", L6.Certs.Ce259d50945779b9d), ("e72b986f4c9e511e", L6.Certs.Ce72b986f4c9e511e), ("ecdc3c4e37764455", L6.Certs.Cecdc3c4e37764455), ("eead66d0c28971eb", L6.Certs.Ceead66d0c28971eb), ("ef762e83bc6e8077", L6.Certs.Cef762e83bc6e8077), ("f6344910dd62038d", L6.Certs.Cf6344910dd62038d), ("fc95884a5bb38035", L6.Certs.Cfc95884a5bb38035)]
    27000 28500 { single := 729, core1 := 771, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
