import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C05b8f74d17bf797e
import L6Check.Certs.C062f626c7e3da160
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C147b955ca1b11d54
import L6Check.Certs.C16c607738140b7f4
import L6Check.Certs.C2541da28357df072
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C26111d499f6cbb56
import L6Check.Certs.C3f0a1164520df5d4
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C60742c0aa412da86
import L6Check.Certs.C6ff53cb44584c94d
import L6Check.Certs.C7972111a1147fdc1
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C9628474d1bbc72e2
import L6Check.Certs.C9994472ee3a3df0a
import L6Check.Certs.C9b5cd75375f980af
import L6Check.Certs.C9cf09299a811d19a
import L6Check.Certs.Ca1c2e7d7424df28c
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cbb253f5966cad766
import L6Check.Certs.Cbf27248691902ac4
import L6Check.Certs.Cc2faacff632573d9
import L6Check.Certs.Cd363b7180a66c9b5
import L6Check.Certs.Cd58c2739d1f6d5ce
import L6Check.Certs.Cd9a736f1204bda12
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce11b7354ea07bda3
import L6Check.Certs.Ceedc750066093d4f
import L6Check.Certs.Cf540916dd67cef28
import L6Check.Certs.Cfb26a2f26815b2d8

/-! F3/F4 (Proposition 5.3), class 128, cells 0 ≤ cell < 1500 of `data/cells/c128.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1500` of class 128 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1234, core1 := 266, core2 := 0, opn := 0 }. -/
theorem F34_c128_k0 : checkChunk 128 n6 cells_128 single_128 links_128 pass_128 open43
    [("05b8f74d17bf797e", L6.Certs.C05b8f74d17bf797e), ("062f626c7e3da160", L6.Certs.C062f626c7e3da160), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("147b955ca1b11d54", L6.Certs.C147b955ca1b11d54), ("16c607738140b7f4", L6.Certs.C16c607738140b7f4), ("2541da28357df072", L6.Certs.C2541da28357df072), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("26111d499f6cbb56", L6.Certs.C26111d499f6cbb56), ("3f0a1164520df5d4", L6.Certs.C3f0a1164520df5d4), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("60742c0aa412da86", L6.Certs.C60742c0aa412da86), ("6ff53cb44584c94d", L6.Certs.C6ff53cb44584c94d), ("7972111a1147fdc1", L6.Certs.C7972111a1147fdc1), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("9628474d1bbc72e2", L6.Certs.C9628474d1bbc72e2), ("9994472ee3a3df0a", L6.Certs.C9994472ee3a3df0a), ("9b5cd75375f980af", L6.Certs.C9b5cd75375f980af), ("9cf09299a811d19a", L6.Certs.C9cf09299a811d19a), ("a1c2e7d7424df28c", L6.Certs.Ca1c2e7d7424df28c), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("bb253f5966cad766", L6.Certs.Cbb253f5966cad766), ("bf27248691902ac4", L6.Certs.Cbf27248691902ac4), ("c2faacff632573d9", L6.Certs.Cc2faacff632573d9), ("d363b7180a66c9b5", L6.Certs.Cd363b7180a66c9b5), ("d58c2739d1f6d5ce", L6.Certs.Cd58c2739d1f6d5ce), ("d9a736f1204bda12", L6.Certs.Cd9a736f1204bda12), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e11b7354ea07bda3", L6.Certs.Ce11b7354ea07bda3), ("eedc750066093d4f", L6.Certs.Ceedc750066093d4f), ("f540916dd67cef28", L6.Certs.Cf540916dd67cef28), ("fb26a2f26815b2d8", L6.Certs.Cfb26a2f26815b2d8)]
    0 1500 { single := 1234, core1 := 266, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
