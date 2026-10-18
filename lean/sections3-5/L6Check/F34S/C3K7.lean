import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C3
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C19d38dfc5b5bd161
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C2f70bd856f06e65e
import L6Check.Certs.C2fc74d4784f04bdc
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C417511092a5c791b
import L6Check.Certs.C45c07671fbddc583
import L6Check.Certs.C4ebde189bca24a5d
import L6Check.Certs.C534b536c8c5ed01a
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5d00be4fed6c02b8
import L6Check.Certs.C5dbbd657f0c793b8
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C66a6f01c6c630892
import L6Check.Certs.C6f2cc1b33a8fa04f
import L6Check.Certs.C723df1cf0ce65998
import L6Check.Certs.C7a8fae3b2b9f37ac
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C8e65bfc835be8eb5
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C9527f5078d959d6e
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9f934353b11c4414
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca84f8289d609b1f8
import L6Check.Certs.Cb2d472bf2c8d0efe
import L6Check.Certs.Cb749fbff1b9592be
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc64b454a8c5e86fd
import L6Check.Certs.Cd5031dceb8d90233
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce3e8d223b87fe872
import L6Check.Certs.Cefa2e2bcd1dc637d
import L6Check.Certs.Cf31caf145c41a79c
import L6Check.Certs.Cf71c6f57d0fa0dab
import L6Check.Certs.Cfbedd87aeefec129

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 3, cells 10500 ≤ cell < 12000 of
`data/cells/c3.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `10500 ≤ cell < 12000` of class 3 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 801, core1 := 699, core2 := 0, opn := 0 }. -/
theorem F34S_c3_k7 : checkChunkS 3 (L6.F2.diagOf 3) L6.F2.Data.cells_c3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("19d38dfc5b5bd161", L6.Certs.C19d38dfc5b5bd161), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("2f70bd856f06e65e", L6.Certs.C2f70bd856f06e65e), ("2fc74d4784f04bdc", L6.Certs.C2fc74d4784f04bdc), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("417511092a5c791b", L6.Certs.C417511092a5c791b), ("45c07671fbddc583", L6.Certs.C45c07671fbddc583), ("4ebde189bca24a5d", L6.Certs.C4ebde189bca24a5d), ("534b536c8c5ed01a", L6.Certs.C534b536c8c5ed01a), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5d00be4fed6c02b8", L6.Certs.C5d00be4fed6c02b8), ("5dbbd657f0c793b8", L6.Certs.C5dbbd657f0c793b8), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("66a6f01c6c630892", L6.Certs.C66a6f01c6c630892), ("6f2cc1b33a8fa04f", L6.Certs.C6f2cc1b33a8fa04f), ("723df1cf0ce65998", L6.Certs.C723df1cf0ce65998), ("7a8fae3b2b9f37ac", L6.Certs.C7a8fae3b2b9f37ac), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("8e65bfc835be8eb5", L6.Certs.C8e65bfc835be8eb5), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("9527f5078d959d6e", L6.Certs.C9527f5078d959d6e), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9f934353b11c4414", L6.Certs.C9f934353b11c4414), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a84f8289d609b1f8", L6.Certs.Ca84f8289d609b1f8), ("b2d472bf2c8d0efe", L6.Certs.Cb2d472bf2c8d0efe), ("b749fbff1b9592be", L6.Certs.Cb749fbff1b9592be), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c64b454a8c5e86fd", L6.Certs.Cc64b454a8c5e86fd), ("d5031dceb8d90233", L6.Certs.Cd5031dceb8d90233), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e3e8d223b87fe872", L6.Certs.Ce3e8d223b87fe872), ("efa2e2bcd1dc637d", L6.Certs.Cefa2e2bcd1dc637d), ("f31caf145c41a79c", L6.Certs.Cf31caf145c41a79c), ("f71c6f57d0fa0dab", L6.Certs.Cf71c6f57d0fa0dab), ("fbedd87aeefec129", L6.Certs.Cfbedd87aeefec129)]
    10500 12000 { single := 801, core1 := 699, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
