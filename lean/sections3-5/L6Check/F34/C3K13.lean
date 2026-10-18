import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C14388f47e4573dd4
import L6Check.Certs.C19982265bc07bf29
import L6Check.Certs.C1a140fd715c8977d
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C2e9e3505b7135c9c
import L6Check.Certs.C3058c17cac9a07d0
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C3f1fbdf123aac18e
import L6Check.Certs.C417511092a5c791b
import L6Check.Certs.C449a597596e67f40
import L6Check.Certs.C45c07671fbddc583
import L6Check.Certs.C496954832531bb6e
import L6Check.Certs.C4b5663adfaab47db
import L6Check.Certs.C5038acf7c79a60be
import L6Check.Certs.C5666f51eb41b85c3
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5a12e6ae2f834977
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C665f3320a997b0ab
import L6Check.Certs.C680c1fc404f586cf
import L6Check.Certs.C72112d56716fc785
import L6Check.Certs.C78a98147aa1211a5
import L6Check.Certs.C8351297e112bdabc
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9b9bbf8a21ffc7e0
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca12d97d2fcf138b4
import L6Check.Certs.Ca32faa1664f2a77c
import L6Check.Certs.Cb13f8818d65a6e8a
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc141c278d23fd57b
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Ccab293f86c688990
import L6Check.Certs.Cce07296cae588c90
import L6Check.Certs.Cd225792bede077bc
import L6Check.Certs.Cd5031dceb8d90233
import L6Check.Certs.Cd9ad20a9ad3ca819
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Cdfb1b2e94c6eef8c
import L6Check.Certs.Ce19b2a24eaa6858b
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ceec5c14bfe01d713
import L6Check.Certs.Cefa2e2bcd1dc637d
import L6Check.Certs.Cf64ab3339f8f6001
import L6Check.Certs.Cf8f4837df18cddcb
import L6Check.Certs.Cfd9bc42758af80b7

/-! F3/F4 (Proposition 5.3), class 3, cells 19500 ≤ cell < 21000 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `19500 ≤ cell < 21000` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 968, core1 := 532, core2 := 0, opn := 0 }. -/
theorem F34_c3_k13 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("14388f47e4573dd4", L6.Certs.C14388f47e4573dd4), ("19982265bc07bf29", L6.Certs.C19982265bc07bf29), ("1a140fd715c8977d", L6.Certs.C1a140fd715c8977d), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("2e9e3505b7135c9c", L6.Certs.C2e9e3505b7135c9c), ("3058c17cac9a07d0", L6.Certs.C3058c17cac9a07d0), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("3f1fbdf123aac18e", L6.Certs.C3f1fbdf123aac18e), ("417511092a5c791b", L6.Certs.C417511092a5c791b), ("449a597596e67f40", L6.Certs.C449a597596e67f40), ("45c07671fbddc583", L6.Certs.C45c07671fbddc583), ("496954832531bb6e", L6.Certs.C496954832531bb6e), ("4b5663adfaab47db", L6.Certs.C4b5663adfaab47db), ("5038acf7c79a60be", L6.Certs.C5038acf7c79a60be), ("5666f51eb41b85c3", L6.Certs.C5666f51eb41b85c3), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5a12e6ae2f834977", L6.Certs.C5a12e6ae2f834977), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("665f3320a997b0ab", L6.Certs.C665f3320a997b0ab), ("680c1fc404f586cf", L6.Certs.C680c1fc404f586cf), ("72112d56716fc785", L6.Certs.C72112d56716fc785), ("78a98147aa1211a5", L6.Certs.C78a98147aa1211a5), ("8351297e112bdabc", L6.Certs.C8351297e112bdabc), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9b9bbf8a21ffc7e0", L6.Certs.C9b9bbf8a21ffc7e0), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a12d97d2fcf138b4", L6.Certs.Ca12d97d2fcf138b4), ("a32faa1664f2a77c", L6.Certs.Ca32faa1664f2a77c), ("b13f8818d65a6e8a", L6.Certs.Cb13f8818d65a6e8a), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c141c278d23fd57b", L6.Certs.Cc141c278d23fd57b), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("cab293f86c688990", L6.Certs.Ccab293f86c688990), ("ce07296cae588c90", L6.Certs.Cce07296cae588c90), ("d225792bede077bc", L6.Certs.Cd225792bede077bc), ("d5031dceb8d90233", L6.Certs.Cd5031dceb8d90233), ("d9ad20a9ad3ca819", L6.Certs.Cd9ad20a9ad3ca819), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("dfb1b2e94c6eef8c", L6.Certs.Cdfb1b2e94c6eef8c), ("e19b2a24eaa6858b", L6.Certs.Ce19b2a24eaa6858b), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("eec5c14bfe01d713", L6.Certs.Ceec5c14bfe01d713), ("efa2e2bcd1dc637d", L6.Certs.Cefa2e2bcd1dc637d), ("f64ab3339f8f6001", L6.Certs.Cf64ab3339f8f6001), ("f8f4837df18cddcb", L6.Certs.Cf8f4837df18cddcb), ("fd9bc42758af80b7", L6.Certs.Cfd9bc42758af80b7)]
    19500 21000 { single := 968, core1 := 532, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
