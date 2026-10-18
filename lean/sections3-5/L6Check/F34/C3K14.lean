import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C19d38dfc5b5bd161
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C24ef7d36a3ea9395
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C2ae537259cb7967a
import L6Check.Certs.C391c3c7fc731914e
import L6Check.Certs.C496954832531bb6e
import L6Check.Certs.C4ebde189bca24a5d
import L6Check.Certs.C4f738a6a99fb6160
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5a12e6ae2f834977
import L6Check.Certs.C5dbbd657f0c793b8
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C665f3320a997b0ab
import L6Check.Certs.C66a6f01c6c630892
import L6Check.Certs.C66f90ff44a8685b9
import L6Check.Certs.C7304f09559b137ec
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9b9bbf8a21ffc7e0
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Cb5c8408e2ec0ac59
import L6Check.Certs.Cb749fbff1b9592be
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Cc56106aa35eca7b4
import L6Check.Certs.Ccfeebf1b9800ac73
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Cdfb1b2e94c6eef8c
import L6Check.Certs.Cf8f4837df18cddcb
import L6Check.Certs.Cfbedd87aeefec129

/-! F3/F4 (Proposition 5.3), class 3, cells 21000 ≤ cell < 22500 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `21000 ≤ cell < 22500` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 896, core1 := 604, core2 := 0, opn := 0 }. -/
theorem F34_c3_k14 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("19d38dfc5b5bd161", L6.Certs.C19d38dfc5b5bd161), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("24ef7d36a3ea9395", L6.Certs.C24ef7d36a3ea9395), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("2ae537259cb7967a", L6.Certs.C2ae537259cb7967a), ("391c3c7fc731914e", L6.Certs.C391c3c7fc731914e), ("496954832531bb6e", L6.Certs.C496954832531bb6e), ("4ebde189bca24a5d", L6.Certs.C4ebde189bca24a5d), ("4f738a6a99fb6160", L6.Certs.C4f738a6a99fb6160), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5a12e6ae2f834977", L6.Certs.C5a12e6ae2f834977), ("5dbbd657f0c793b8", L6.Certs.C5dbbd657f0c793b8), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("665f3320a997b0ab", L6.Certs.C665f3320a997b0ab), ("66a6f01c6c630892", L6.Certs.C66a6f01c6c630892), ("66f90ff44a8685b9", L6.Certs.C66f90ff44a8685b9), ("7304f09559b137ec", L6.Certs.C7304f09559b137ec), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9b9bbf8a21ffc7e0", L6.Certs.C9b9bbf8a21ffc7e0), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("b5c8408e2ec0ac59", L6.Certs.Cb5c8408e2ec0ac59), ("b749fbff1b9592be", L6.Certs.Cb749fbff1b9592be), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("c56106aa35eca7b4", L6.Certs.Cc56106aa35eca7b4), ("cfeebf1b9800ac73", L6.Certs.Ccfeebf1b9800ac73), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("dfb1b2e94c6eef8c", L6.Certs.Cdfb1b2e94c6eef8c), ("f8f4837df18cddcb", L6.Certs.Cf8f4837df18cddcb), ("fbedd87aeefec129", L6.Certs.Cfbedd87aeefec129)]
    21000 22500 { single := 896, core1 := 604, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
