import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C16c607738140b7f4
import L6Check.Certs.C260dc626db027e9c
import L6Check.Certs.C2c9a3c068e6484d5
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C5d23d8880d91e302
import L6Check.Certs.C60742c0aa412da86
import L6Check.Certs.C6b1a1a28c16f82f7
import L6Check.Certs.C6ff53cb44584c94d
import L6Check.Certs.C7972111a1147fdc1
import L6Check.Certs.C7a279a1af6eefd6a
import L6Check.Certs.C879fb5d82e0a8167
import L6Check.Certs.C890f5cb1991f3bc1
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C989a7145b98c6f67
import L6Check.Certs.C996c1c7a419f7259
import L6Check.Certs.C9994472ee3a3df0a
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Cb1b16685f4f8475e
import L6Check.Certs.Cb35d51d17031c848
import L6Check.Certs.Ccf20072e83aaa6fb
import L6Check.Certs.Cd363b7180a66c9b5
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cdc8b9573655396e4
import L6Check.Certs.Ce11b7354ea07bda3
import L6Check.Certs.Ce8784e87640f9396
import L6Check.Certs.Cec1eb8fb7dbe3ee8
import L6Check.Certs.Cf28b79cf11a54956
import L6Check.Certs.Cfb26a2f26815b2d8

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 12000 ≤ cell < 13500 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `12000 ≤ cell < 13500` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1234, core1 := 266, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k8 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("16c607738140b7f4", L6.Certs.C16c607738140b7f4), ("260dc626db027e9c", L6.Certs.C260dc626db027e9c), ("2c9a3c068e6484d5", L6.Certs.C2c9a3c068e6484d5), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("5d23d8880d91e302", L6.Certs.C5d23d8880d91e302), ("60742c0aa412da86", L6.Certs.C60742c0aa412da86), ("6b1a1a28c16f82f7", L6.Certs.C6b1a1a28c16f82f7), ("6ff53cb44584c94d", L6.Certs.C6ff53cb44584c94d), ("7972111a1147fdc1", L6.Certs.C7972111a1147fdc1), ("7a279a1af6eefd6a", L6.Certs.C7a279a1af6eefd6a), ("879fb5d82e0a8167", L6.Certs.C879fb5d82e0a8167), ("890f5cb1991f3bc1", L6.Certs.C890f5cb1991f3bc1), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("989a7145b98c6f67", L6.Certs.C989a7145b98c6f67), ("996c1c7a419f7259", L6.Certs.C996c1c7a419f7259), ("9994472ee3a3df0a", L6.Certs.C9994472ee3a3df0a), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("b1b16685f4f8475e", L6.Certs.Cb1b16685f4f8475e), ("b35d51d17031c848", L6.Certs.Cb35d51d17031c848), ("cf20072e83aaa6fb", L6.Certs.Ccf20072e83aaa6fb), ("d363b7180a66c9b5", L6.Certs.Cd363b7180a66c9b5), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("dc8b9573655396e4", L6.Certs.Cdc8b9573655396e4), ("e11b7354ea07bda3", L6.Certs.Ce11b7354ea07bda3), ("e8784e87640f9396", L6.Certs.Ce8784e87640f9396), ("ec1eb8fb7dbe3ee8", L6.Certs.Cec1eb8fb7dbe3ee8), ("f28b79cf11a54956", L6.Certs.Cf28b79cf11a54956), ("fb26a2f26815b2d8", L6.Certs.Cfb26a2f26815b2d8)]
    12000 13500 { single := 1234, core1 := 266, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
