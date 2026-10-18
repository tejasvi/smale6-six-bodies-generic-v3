import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C47
import L6Check.F34.Data.Common
import L6Check.F34.Data.C47
import L6Check.Certs.C0fd6de36cae427b6
import L6Check.Certs.C1f349951f9365773
import L6Check.Certs.C318e8a21f64c5056
import L6Check.Certs.C3b346da30054d354
import L6Check.Certs.C495be6eb51908b56
import L6Check.Certs.C72bda3e4fa7395a9
import L6Check.Certs.C800cd85c5d304ca7
import L6Check.Certs.C8857db9784f0fc0c
import L6Check.Certs.C89f4fe76352d8c88
import L6Check.Certs.C8f96fd9e030fe785
import L6Check.Certs.C97121063ae53a37e
import L6Check.Certs.Ca88bafa2f0f7be8f
import L6Check.Certs.Cb4c608a1aaa1e4dc
import L6Check.Certs.Cbc3c5244b70145a9
import L6Check.Certs.Cd2cd3ca81a5113d7
import L6Check.Certs.Cd6adf1902728df7c
import L6Check.Certs.Ce05e25b1d5d2a37d
import L6Check.Certs.Ce0c347ffe400acf0
import L6Check.Certs.Ce1af5693348581b1

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 47, cells 0 ≤ cell < 497 of
`data/cells/c47.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 497` of class 47 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 128, core1 := 369, core2 := 0, opn := 0 }. -/
theorem F34S_c47_k0 : checkChunkS 47 (L6.F2.diagOf 47) L6.F2.Data.cells_c47 single_47 links_47 pass_47 open43
    [("0fd6de36cae427b6", L6.Certs.C0fd6de36cae427b6), ("1f349951f9365773", L6.Certs.C1f349951f9365773), ("318e8a21f64c5056", L6.Certs.C318e8a21f64c5056), ("3b346da30054d354", L6.Certs.C3b346da30054d354), ("495be6eb51908b56", L6.Certs.C495be6eb51908b56), ("72bda3e4fa7395a9", L6.Certs.C72bda3e4fa7395a9), ("800cd85c5d304ca7", L6.Certs.C800cd85c5d304ca7), ("8857db9784f0fc0c", L6.Certs.C8857db9784f0fc0c), ("89f4fe76352d8c88", L6.Certs.C89f4fe76352d8c88), ("8f96fd9e030fe785", L6.Certs.C8f96fd9e030fe785), ("97121063ae53a37e", L6.Certs.C97121063ae53a37e), ("a88bafa2f0f7be8f", L6.Certs.Ca88bafa2f0f7be8f), ("b4c608a1aaa1e4dc", L6.Certs.Cb4c608a1aaa1e4dc), ("bc3c5244b70145a9", L6.Certs.Cbc3c5244b70145a9), ("d2cd3ca81a5113d7", L6.Certs.Cd2cd3ca81a5113d7), ("d6adf1902728df7c", L6.Certs.Cd6adf1902728df7c), ("e05e25b1d5d2a37d", L6.Certs.Ce05e25b1d5d2a37d), ("e0c347ffe400acf0", L6.Certs.Ce0c347ffe400acf0), ("e1af5693348581b1", L6.Certs.Ce1af5693348581b1)]
    0 497 { single := 128, core1 := 369, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
