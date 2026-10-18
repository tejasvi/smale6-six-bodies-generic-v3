import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C150
import L6Check.F34.Data.Common
import L6Check.F34.Data.C150
import L6Check.Certs.C0d84218e6efa3052
import L6Check.Certs.C2e4383462f92db6b
import L6Check.Certs.C392aea6662b7eaef
import L6Check.Certs.C3c5862a0087ddea1
import L6Check.Certs.C53c8b2ddab2b632b
import L6Check.Certs.C672aeb0321a50384
import L6Check.Certs.C87646cfb8291a9c0
import L6Check.Certs.C90b5f3b832d0780c
import L6Check.Certs.Ca852b6f1c1c7de3e
import L6Check.Certs.Cb1a8296b2bd2b206
import L6Check.Certs.Cb8869a68e220593f
import L6Check.Certs.Cbda63b1c3bf83f47
import L6Check.Certs.Cc0b2acc0d217d09a
import L6Check.Certs.Cc423f02ddcf0a15b
import L6Check.Certs.Cd30bf77ee6877a5c
import L6Check.Certs.Cd58c2739d1f6d5ce
import L6Check.Certs.Cd78e7bac0db324a1
import L6Check.Certs.Cf28b79cf11a54956
import L6Check.Certs.Cf75f12324fc8638c

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 150, cells 0 ≤ cell < 224 of
`data/cells/c150.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 224` of class 150 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 0, core1 := 224, core2 := 0, opn := 0 }. -/
theorem F34S_c150_k0 : checkChunkS 150 (L6.F2.diagOf 150) L6.F2.Data.cells_c150 single_150 links_150 pass_150 open43
    [("0d84218e6efa3052", L6.Certs.C0d84218e6efa3052), ("2e4383462f92db6b", L6.Certs.C2e4383462f92db6b), ("392aea6662b7eaef", L6.Certs.C392aea6662b7eaef), ("3c5862a0087ddea1", L6.Certs.C3c5862a0087ddea1), ("53c8b2ddab2b632b", L6.Certs.C53c8b2ddab2b632b), ("672aeb0321a50384", L6.Certs.C672aeb0321a50384), ("87646cfb8291a9c0", L6.Certs.C87646cfb8291a9c0), ("90b5f3b832d0780c", L6.Certs.C90b5f3b832d0780c), ("a852b6f1c1c7de3e", L6.Certs.Ca852b6f1c1c7de3e), ("b1a8296b2bd2b206", L6.Certs.Cb1a8296b2bd2b206), ("b8869a68e220593f", L6.Certs.Cb8869a68e220593f), ("bda63b1c3bf83f47", L6.Certs.Cbda63b1c3bf83f47), ("c0b2acc0d217d09a", L6.Certs.Cc0b2acc0d217d09a), ("c423f02ddcf0a15b", L6.Certs.Cc423f02ddcf0a15b), ("d30bf77ee6877a5c", L6.Certs.Cd30bf77ee6877a5c), ("d58c2739d1f6d5ce", L6.Certs.Cd58c2739d1f6d5ce), ("d78e7bac0db324a1", L6.Certs.Cd78e7bac0db324a1), ("f28b79cf11a54956", L6.Certs.Cf28b79cf11a54956), ("f75f12324fc8638c", L6.Certs.Cf75f12324fc8638c)]
    0 224 { single := 0, core1 := 224, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
