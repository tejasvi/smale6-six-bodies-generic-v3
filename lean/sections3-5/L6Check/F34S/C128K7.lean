import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C04b1474bc3439753
import L6Check.Certs.C1c5646413b43d31b
import L6Check.Certs.C1e35066014af680f
import L6Check.Certs.C30184054f51d9e96
import L6Check.Certs.C51ee843597cff9f3
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C58744aa197893a83
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C724a7accb412014a
import L6Check.Certs.Ca0269f9ead157d0c
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cb0798c2bf2ea25ad
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce80b80e4cb5ae9fe
import L6Check.Certs.Cfab0e5212c8d3c79

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 10500 ≤ cell < 12000 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `10500 ≤ cell < 12000` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1144, core1 := 356, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k7 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("04b1474bc3439753", L6.Certs.C04b1474bc3439753), ("1c5646413b43d31b", L6.Certs.C1c5646413b43d31b), ("1e35066014af680f", L6.Certs.C1e35066014af680f), ("30184054f51d9e96", L6.Certs.C30184054f51d9e96), ("51ee843597cff9f3", L6.Certs.C51ee843597cff9f3), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("58744aa197893a83", L6.Certs.C58744aa197893a83), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("724a7accb412014a", L6.Certs.C724a7accb412014a), ("a0269f9ead157d0c", L6.Certs.Ca0269f9ead157d0c), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("b0798c2bf2ea25ad", L6.Certs.Cb0798c2bf2ea25ad), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e80b80e4cb5ae9fe", L6.Certs.Ce80b80e4cb5ae9fe), ("fab0e5212c8d3c79", L6.Certs.Cfab0e5212c8d3c79)]
    10500 12000 { single := 1144, core1 := 356, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
