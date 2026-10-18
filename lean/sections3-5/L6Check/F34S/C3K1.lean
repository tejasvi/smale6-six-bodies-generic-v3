import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C3
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C1154f63f4ae46ba1
import L6Check.Certs.C191808cadf41376a
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C391c3c7fc731914e
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.C496954832531bb6e
import L6Check.Certs.C4ebde189bca24a5d
import L6Check.Certs.C5038acf7c79a60be
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C67f91604077639fb
import L6Check.Certs.C6ab714f4d84692a6
import L6Check.Certs.C6cb81b64dfa2ff3a
import L6Check.Certs.C7f10f1f3767082da
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C895c61d3288b6eef
import L6Check.Certs.C897da59625543f7b
import L6Check.Certs.C99c63b41316cf3a6
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca05f78c08e847399
import L6Check.Certs.Ca561a929e7e499f5
import L6Check.Certs.Cb749fbff1b9592be
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Cc8ef113f686cf0c4
import L6Check.Certs.Cdd3879243137f416
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Cde0327302cbb87f4
import L6Check.Certs.Ce259d50945779b9d
import L6Check.Certs.Ce36e575c21c81dd7
import L6Check.Certs.Cecdc3c4e37764455
import L6Check.Certs.Cef762e83bc6e8077
import L6Check.Certs.Cf6344910dd62038d
import L6Check.Certs.Cf9d89ba1685be5ab
import L6Check.Certs.Cfbedd87aeefec129

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 3, cells 1500 ≤ cell < 3000 of
`data/cells/c3.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `1500 ≤ cell < 3000` of class 3 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1019, core1 := 481, core2 := 0, opn := 0 }. -/
theorem F34S_c3_k1 : checkChunkS 3 (L6.F2.diagOf 3) L6.F2.Data.cells_c3 single_3 links_3 pass_3 open43
    [("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("1154f63f4ae46ba1", L6.Certs.C1154f63f4ae46ba1), ("191808cadf41376a", L6.Certs.C191808cadf41376a), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("391c3c7fc731914e", L6.Certs.C391c3c7fc731914e), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("496954832531bb6e", L6.Certs.C496954832531bb6e), ("4ebde189bca24a5d", L6.Certs.C4ebde189bca24a5d), ("5038acf7c79a60be", L6.Certs.C5038acf7c79a60be), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("67f91604077639fb", L6.Certs.C67f91604077639fb), ("6ab714f4d84692a6", L6.Certs.C6ab714f4d84692a6), ("6cb81b64dfa2ff3a", L6.Certs.C6cb81b64dfa2ff3a), ("7f10f1f3767082da", L6.Certs.C7f10f1f3767082da), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("895c61d3288b6eef", L6.Certs.C895c61d3288b6eef), ("897da59625543f7b", L6.Certs.C897da59625543f7b), ("99c63b41316cf3a6", L6.Certs.C99c63b41316cf3a6), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a05f78c08e847399", L6.Certs.Ca05f78c08e847399), ("a561a929e7e499f5", L6.Certs.Ca561a929e7e499f5), ("b749fbff1b9592be", L6.Certs.Cb749fbff1b9592be), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("c8ef113f686cf0c4", L6.Certs.Cc8ef113f686cf0c4), ("dd3879243137f416", L6.Certs.Cdd3879243137f416), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("de0327302cbb87f4", L6.Certs.Cde0327302cbb87f4), ("e259d50945779b9d", L6.Certs.Ce259d50945779b9d), ("e36e575c21c81dd7", L6.Certs.Ce36e575c21c81dd7), ("ecdc3c4e37764455", L6.Certs.Cecdc3c4e37764455), ("ef762e83bc6e8077", L6.Certs.Cef762e83bc6e8077), ("f6344910dd62038d", L6.Certs.Cf6344910dd62038d), ("f9d89ba1685be5ab", L6.Certs.Cf9d89ba1685be5ab), ("fbedd87aeefec129", L6.Certs.Cfbedd87aeefec129)]
    1500 3000 { single := 1019, core1 := 481, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
