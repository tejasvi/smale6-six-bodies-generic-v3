import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C26111d499f6cbb56
import L6Check.Certs.C27936f58af22e07b
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C2d98fc5276cebdd8
import L6Check.Certs.C3f0a1164520df5d4
import L6Check.Certs.C46bb7d1d47186aa8
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C57c2b2f3ce64f2cc
import L6Check.Certs.C7a279a1af6eefd6a
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C9628474d1bbc72e2
import L6Check.Certs.C9cf09299a811d19a
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cb33ea2b4c1c341f9
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Cc2faacff632573d9
import L6Check.Certs.Cd58c2739d1f6d5ce
import L6Check.Certs.Cd9a736f1204bda12
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cdd4ee89766f77311
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Ceedc750066093d4f
import L6Check.Certs.Cf540916dd67cef28

/-! F3/F4 (Proposition 5.3), class 128, cells 1500 ≤ cell < 3000 of `data/cells/c128.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `1500 ≤ cell < 3000` of class 128 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1286, core1 := 214, core2 := 0, opn := 0 }. -/
theorem F34_c128_k1 : checkChunk 128 n6 cells_128 single_128 links_128 pass_128 open43
    [("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("26111d499f6cbb56", L6.Certs.C26111d499f6cbb56), ("27936f58af22e07b", L6.Certs.C27936f58af22e07b), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("2d98fc5276cebdd8", L6.Certs.C2d98fc5276cebdd8), ("3f0a1164520df5d4", L6.Certs.C3f0a1164520df5d4), ("46bb7d1d47186aa8", L6.Certs.C46bb7d1d47186aa8), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("57c2b2f3ce64f2cc", L6.Certs.C57c2b2f3ce64f2cc), ("7a279a1af6eefd6a", L6.Certs.C7a279a1af6eefd6a), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("9628474d1bbc72e2", L6.Certs.C9628474d1bbc72e2), ("9cf09299a811d19a", L6.Certs.C9cf09299a811d19a), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("b33ea2b4c1c341f9", L6.Certs.Cb33ea2b4c1c341f9), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("c2faacff632573d9", L6.Certs.Cc2faacff632573d9), ("d58c2739d1f6d5ce", L6.Certs.Cd58c2739d1f6d5ce), ("d9a736f1204bda12", L6.Certs.Cd9a736f1204bda12), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("dd4ee89766f77311", L6.Certs.Cdd4ee89766f77311), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("eedc750066093d4f", L6.Certs.Ceedc750066093d4f), ("f540916dd67cef28", L6.Certs.Cf540916dd67cef28)]
    1500 3000 { single := 1286, core1 := 214, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
