import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C260dc626db027e9c
import L6Check.Certs.C2d98fc5276cebdd8
import L6Check.Certs.C46bb7d1d47186aa8
import L6Check.Certs.C5d23d8880d91e302
import L6Check.Certs.C60742c0aa412da86
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C6b1a1a28c16f82f7
import L6Check.Certs.C7972111a1147fdc1
import L6Check.Certs.C879fb5d82e0a8167
import L6Check.Certs.C890f5cb1991f3bc1
import L6Check.Certs.C996c1c7a419f7259
import L6Check.Certs.C9c8c9c595dbe19d3
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca697e155eadbb939
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cb1b16685f4f8475e
import L6Check.Certs.Cbf1c1072d313dea1
import L6Check.Certs.Ccf20072e83aaa6fb
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Cdc8b9573655396e4
import L6Check.Certs.Cdd4ee89766f77311
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Cfb26a2f26815b2d8

/-! F3/F4 (Proposition 5.3), class 128, cells 13500 ≤ cell < 15000 of `data/cells/c128.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `13500 ≤ cell < 15000` of class 128 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1185, core1 := 315, core2 := 0, opn := 0 }. -/
theorem F34_c128_k9 : checkChunk 128 n6 cells_128 single_128 links_128 pass_128 open43
    [("260dc626db027e9c", L6.Certs.C260dc626db027e9c), ("2d98fc5276cebdd8", L6.Certs.C2d98fc5276cebdd8), ("46bb7d1d47186aa8", L6.Certs.C46bb7d1d47186aa8), ("5d23d8880d91e302", L6.Certs.C5d23d8880d91e302), ("60742c0aa412da86", L6.Certs.C60742c0aa412da86), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("6b1a1a28c16f82f7", L6.Certs.C6b1a1a28c16f82f7), ("7972111a1147fdc1", L6.Certs.C7972111a1147fdc1), ("879fb5d82e0a8167", L6.Certs.C879fb5d82e0a8167), ("890f5cb1991f3bc1", L6.Certs.C890f5cb1991f3bc1), ("996c1c7a419f7259", L6.Certs.C996c1c7a419f7259), ("9c8c9c595dbe19d3", L6.Certs.C9c8c9c595dbe19d3), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a697e155eadbb939", L6.Certs.Ca697e155eadbb939), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("b1b16685f4f8475e", L6.Certs.Cb1b16685f4f8475e), ("bf1c1072d313dea1", L6.Certs.Cbf1c1072d313dea1), ("cf20072e83aaa6fb", L6.Certs.Ccf20072e83aaa6fb), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("dc8b9573655396e4", L6.Certs.Cdc8b9573655396e4), ("dd4ee89766f77311", L6.Certs.Cdd4ee89766f77311), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("fb26a2f26815b2d8", L6.Certs.Cfb26a2f26815b2d8)]
    13500 15000 { single := 1185, core1 := 315, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
