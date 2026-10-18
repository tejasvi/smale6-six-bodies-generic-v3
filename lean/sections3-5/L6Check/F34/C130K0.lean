import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C130
import L6Check.Certs.C0d56962ac8bf9111
import L6Check.Certs.C11b1691f381e26bc
import L6Check.Certs.C19e3c019fbfb7ff3
import L6Check.Certs.C1e35066014af680f
import L6Check.Certs.C4182694dbabca56f
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C661441e082bf5fdc
import L6Check.Certs.C762e234028654acf
import L6Check.Certs.C7758d47761d69fc2
import L6Check.Certs.C8185764ed1fa3d6a
import L6Check.Certs.C840c96f3ce3e4567
import L6Check.Certs.C9dcc5b5558322086
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Cb0798c2bf2ea25ad
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cda6cee4a2afc7687
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce15e707b5b269e6d
import L6Check.Certs.Ceb42df4682c799fd
import L6Check.Certs.Cf6d365aab0daf77f

/-! F3/F4 (Proposition 5.3), class 130, cells 0 ≤ cell < 630 of `data/cells/c130.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 630` of class 130 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 0, core1 := 630, core2 := 0, opn := 0 }. -/
theorem F34_c130_k0 : checkChunk 130 n6 cells_130 single_130 links_130 pass_130 open43
    [("0d56962ac8bf9111", L6.Certs.C0d56962ac8bf9111), ("11b1691f381e26bc", L6.Certs.C11b1691f381e26bc), ("19e3c019fbfb7ff3", L6.Certs.C19e3c019fbfb7ff3), ("1e35066014af680f", L6.Certs.C1e35066014af680f), ("4182694dbabca56f", L6.Certs.C4182694dbabca56f), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("661441e082bf5fdc", L6.Certs.C661441e082bf5fdc), ("762e234028654acf", L6.Certs.C762e234028654acf), ("7758d47761d69fc2", L6.Certs.C7758d47761d69fc2), ("8185764ed1fa3d6a", L6.Certs.C8185764ed1fa3d6a), ("840c96f3ce3e4567", L6.Certs.C840c96f3ce3e4567), ("9dcc5b5558322086", L6.Certs.C9dcc5b5558322086), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("b0798c2bf2ea25ad", L6.Certs.Cb0798c2bf2ea25ad), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("da6cee4a2afc7687", L6.Certs.Cda6cee4a2afc7687), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e15e707b5b269e6d", L6.Certs.Ce15e707b5b269e6d), ("eb42df4682c799fd", L6.Certs.Ceb42df4682c799fd), ("f6d365aab0daf77f", L6.Certs.Cf6d365aab0daf77f)]
    0 630 { single := 0, core1 := 630, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
