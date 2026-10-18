import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C04b1474bc3439753
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C1e35066014af680f
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C30184054f51d9e96
import L6Check.Certs.C51ee843597cff9f3
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C58744aa197893a83
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C724a7accb412014a
import L6Check.Certs.Ca0269f9ead157d0c
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cadef2fe140d8aa2c
import L6Check.Certs.Caf1fed30ea4811fe
import L6Check.Certs.Cc36787aebb4c42a0
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Cfab0e5212c8d3c79

/-! F3/F4 (Proposition 5.3), class 128, cells 9000 ≤ cell < 10500 of `data/cells/c128.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `9000 ≤ cell < 10500` of class 128 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1276, core1 := 224, core2 := 0, opn := 0 }. -/
theorem F34_c128_k6 : checkChunk 128 n6 cells_128 single_128 links_128 pass_128 open43
    [("04b1474bc3439753", L6.Certs.C04b1474bc3439753), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("1e35066014af680f", L6.Certs.C1e35066014af680f), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("30184054f51d9e96", L6.Certs.C30184054f51d9e96), ("51ee843597cff9f3", L6.Certs.C51ee843597cff9f3), ("558e59d95895105f", L6.Certs.C558e59d95895105f), ("58744aa197893a83", L6.Certs.C58744aa197893a83), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("724a7accb412014a", L6.Certs.C724a7accb412014a), ("a0269f9ead157d0c", L6.Certs.Ca0269f9ead157d0c), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("adef2fe140d8aa2c", L6.Certs.Cadef2fe140d8aa2c), ("af1fed30ea4811fe", L6.Certs.Caf1fed30ea4811fe), ("c36787aebb4c42a0", L6.Certs.Cc36787aebb4c42a0), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("fab0e5212c8d3c79", L6.Certs.Cfab0e5212c8d3c79)]
    9000 10500 { single := 1276, core1 := 224, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
