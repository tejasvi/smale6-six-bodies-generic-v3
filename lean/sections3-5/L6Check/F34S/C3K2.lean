import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C3
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C072807f872160086
import L6Check.Certs.C168bc37380022672
import L6Check.Certs.C169462b19fb5aa18
import L6Check.Certs.C191808cadf41376a
import L6Check.Certs.C19d04dfab9430155
import L6Check.Certs.C19d38dfc5b5bd161
import L6Check.Certs.C1b0590af21cf650a
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C2b1c0bd986785191
import L6Check.Certs.C32895f491bb8c754
import L6Check.Certs.C3c8a58e9032fb031
import L6Check.Certs.C44cdf143fb05a3d2
import L6Check.Certs.C4ebde189bca24a5d
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5dbbd657f0c793b8
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C66a6f01c6c630892
import L6Check.Certs.C67f91604077639fb
import L6Check.Certs.C6c5e96bff34ebc16
import L6Check.Certs.C755fe1ea86810058
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C897da59625543f7b
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C9117280a7ad8e873
import L6Check.Certs.C99c63b41316cf3a6
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca05f78c08e847399
import L6Check.Certs.Ca6ed7986aaba4c74
import L6Check.Certs.Ca9e0d389f1c10de1
import L6Check.Certs.Cbf4defbd90531d84
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cd2055de92341cc0e
import L6Check.Certs.Cdd3879243137f416
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ceead66d0c28971eb
import L6Check.Certs.Cf6344910dd62038d
import L6Check.Certs.Cfa085f9449c88733

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 3, cells 3000 ≤ cell < 4500 of
`data/cells/c3.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `3000 ≤ cell < 4500` of class 3 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 797, core1 := 703, core2 := 0, opn := 0 }. -/
theorem F34S_c3_k2 : checkChunkS 3 (L6.F2.diagOf 3) L6.F2.Data.cells_c3 single_3 links_3 pass_3 open43
    [("07018856a1764b34", L6.Certs.C07018856a1764b34), ("072807f872160086", L6.Certs.C072807f872160086), ("168bc37380022672", L6.Certs.C168bc37380022672), ("169462b19fb5aa18", L6.Certs.C169462b19fb5aa18), ("191808cadf41376a", L6.Certs.C191808cadf41376a), ("19d04dfab9430155", L6.Certs.C19d04dfab9430155), ("19d38dfc5b5bd161", L6.Certs.C19d38dfc5b5bd161), ("1b0590af21cf650a", L6.Certs.C1b0590af21cf650a), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("2b1c0bd986785191", L6.Certs.C2b1c0bd986785191), ("32895f491bb8c754", L6.Certs.C32895f491bb8c754), ("3c8a58e9032fb031", L6.Certs.C3c8a58e9032fb031), ("44cdf143fb05a3d2", L6.Certs.C44cdf143fb05a3d2), ("4ebde189bca24a5d", L6.Certs.C4ebde189bca24a5d), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5dbbd657f0c793b8", L6.Certs.C5dbbd657f0c793b8), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("66a6f01c6c630892", L6.Certs.C66a6f01c6c630892), ("67f91604077639fb", L6.Certs.C67f91604077639fb), ("6c5e96bff34ebc16", L6.Certs.C6c5e96bff34ebc16), ("755fe1ea86810058", L6.Certs.C755fe1ea86810058), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("897da59625543f7b", L6.Certs.C897da59625543f7b), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("9117280a7ad8e873", L6.Certs.C9117280a7ad8e873), ("99c63b41316cf3a6", L6.Certs.C99c63b41316cf3a6), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a05f78c08e847399", L6.Certs.Ca05f78c08e847399), ("a6ed7986aaba4c74", L6.Certs.Ca6ed7986aaba4c74), ("a9e0d389f1c10de1", L6.Certs.Ca9e0d389f1c10de1), ("bf4defbd90531d84", L6.Certs.Cbf4defbd90531d84), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("d2055de92341cc0e", L6.Certs.Cd2055de92341cc0e), ("dd3879243137f416", L6.Certs.Cdd3879243137f416), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("eead66d0c28971eb", L6.Certs.Ceead66d0c28971eb), ("f6344910dd62038d", L6.Certs.Cf6344910dd62038d), ("fa085f9449c88733", L6.Certs.Cfa085f9449c88733)]
    3000 4500 { single := 797, core1 := 703, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
