import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C14d13bb5c15a2ce7
import L6Check.Certs.C19982265bc07bf29
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C20b239b1d7c40682
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C2a9d6dc7e0196a99
import L6Check.Certs.C2e9e3505b7135c9c
import L6Check.Certs.C2fc74d4784f04bdc
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C417511092a5c791b
import L6Check.Certs.C4175ab9d7eca972d
import L6Check.Certs.C44d7aad63192c017
import L6Check.Certs.C45c07671fbddc583
import L6Check.Certs.C534b536c8c5ed01a
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C72112d56716fc785
import L6Check.Certs.C723df1cf0ce65998
import L6Check.Certs.C78a98147aa1211a5
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C9117280a7ad8e873
import L6Check.Certs.C9527f5078d959d6e
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca12d97d2fcf138b4
import L6Check.Certs.Ca32faa1664f2a77c
import L6Check.Certs.Cb13f8818d65a6e8a
import L6Check.Certs.Cb85c01281d745a3f
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc64b454a8c5e86fd
import L6Check.Certs.Cd5031dceb8d90233
import L6Check.Certs.Cd5576d1a61c18946
import L6Check.Certs.Cd8deb7b57e227fe5
import L6Check.Certs.Cd9ad20a9ad3ca819
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Cefa2e2bcd1dc637d
import L6Check.Certs.Cf4789d563aaaab13
import L6Check.Certs.Cf62ee21f9b749c13
import L6Check.Certs.Cf64ab3339f8f6001

/-! F3/F4 (Proposition 5.3), class 3, cells 18000 ≤ cell < 19500 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `18000 ≤ cell < 19500` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 443, core1 := 1057, core2 := 0, opn := 0 }. -/
theorem F34_c3_k12 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("14d13bb5c15a2ce7", L6.Certs.C14d13bb5c15a2ce7), ("19982265bc07bf29", L6.Certs.C19982265bc07bf29), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("20b239b1d7c40682", L6.Certs.C20b239b1d7c40682), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("2a9d6dc7e0196a99", L6.Certs.C2a9d6dc7e0196a99), ("2e9e3505b7135c9c", L6.Certs.C2e9e3505b7135c9c), ("2fc74d4784f04bdc", L6.Certs.C2fc74d4784f04bdc), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("417511092a5c791b", L6.Certs.C417511092a5c791b), ("4175ab9d7eca972d", L6.Certs.C4175ab9d7eca972d), ("44d7aad63192c017", L6.Certs.C44d7aad63192c017), ("45c07671fbddc583", L6.Certs.C45c07671fbddc583), ("534b536c8c5ed01a", L6.Certs.C534b536c8c5ed01a), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("72112d56716fc785", L6.Certs.C72112d56716fc785), ("723df1cf0ce65998", L6.Certs.C723df1cf0ce65998), ("78a98147aa1211a5", L6.Certs.C78a98147aa1211a5), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("9117280a7ad8e873", L6.Certs.C9117280a7ad8e873), ("9527f5078d959d6e", L6.Certs.C9527f5078d959d6e), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a12d97d2fcf138b4", L6.Certs.Ca12d97d2fcf138b4), ("a32faa1664f2a77c", L6.Certs.Ca32faa1664f2a77c), ("b13f8818d65a6e8a", L6.Certs.Cb13f8818d65a6e8a), ("b85c01281d745a3f", L6.Certs.Cb85c01281d745a3f), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c64b454a8c5e86fd", L6.Certs.Cc64b454a8c5e86fd), ("d5031dceb8d90233", L6.Certs.Cd5031dceb8d90233), ("d5576d1a61c18946", L6.Certs.Cd5576d1a61c18946), ("d8deb7b57e227fe5", L6.Certs.Cd8deb7b57e227fe5), ("d9ad20a9ad3ca819", L6.Certs.Cd9ad20a9ad3ca819), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("efa2e2bcd1dc637d", L6.Certs.Cefa2e2bcd1dc637d), ("f4789d563aaaab13", L6.Certs.Cf4789d563aaaab13), ("f62ee21f9b749c13", L6.Certs.Cf62ee21f9b749c13), ("f64ab3339f8f6001", L6.Certs.Cf64ab3339f8f6001)]
    18000 19500 { single := 443, core1 := 1057, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
