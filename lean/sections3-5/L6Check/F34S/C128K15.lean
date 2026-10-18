import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C128
import L6Check.F34.Data.Common
import L6Check.F34.Data.C128
import L6Check.Certs.C04a293a6f93a7c21
import L6Check.Certs.C04b1474bc3439753
import L6Check.Certs.C05e400010015c30b
import L6Check.Certs.C0d9b4539e3fae63d
import L6Check.Certs.C147b955ca1b11d54
import L6Check.Certs.C1d6c9c68b0b30e0d
import L6Check.Certs.C256c4bfd6c086154
import L6Check.Certs.C30184054f51d9e96
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C4f0c91a1caed7fbb
import L6Check.Certs.C51ee843597cff9f3
import L6Check.Certs.C58744aa197893a83
import L6Check.Certs.C5a94e6f179d11010
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C724a7accb412014a
import L6Check.Certs.C83e997a1e6f21d99
import L6Check.Certs.Ca0269f9ead157d0c
import L6Check.Certs.Ca211ae61440c695c
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca70957032f7223f5
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cabe3d270a8beabac
import L6Check.Certs.Cc283f4873b50bcb4
import L6Check.Certs.Cc5e28c7729b266fb
import L6Check.Certs.Ccea573f3b40c98b7
import L6Check.Certs.Cda286d98e1816635
import L6Check.Certs.Ce124815fb09044d8
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Ce80b80e4cb5ae9fe
import L6Check.Certs.Cfab0e5212c8d3c79

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 128, cells 22500 ≤ cell < 24000 of
`data/cells/c128.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `22500 ≤ cell < 24000` of class 128 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 1195, core1 := 305, core2 := 0, opn := 0 }. -/
theorem F34S_c128_k15 : checkChunkS 128 (L6.F2.diagOf 128) L6.F2.Data.cells_c128 single_128 links_128 pass_128 open43
    [("04a293a6f93a7c21", L6.Certs.C04a293a6f93a7c21), ("04b1474bc3439753", L6.Certs.C04b1474bc3439753), ("05e400010015c30b", L6.Certs.C05e400010015c30b), ("0d9b4539e3fae63d", L6.Certs.C0d9b4539e3fae63d), ("147b955ca1b11d54", L6.Certs.C147b955ca1b11d54), ("1d6c9c68b0b30e0d", L6.Certs.C1d6c9c68b0b30e0d), ("256c4bfd6c086154", L6.Certs.C256c4bfd6c086154), ("30184054f51d9e96", L6.Certs.C30184054f51d9e96), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("4f0c91a1caed7fbb", L6.Certs.C4f0c91a1caed7fbb), ("51ee843597cff9f3", L6.Certs.C51ee843597cff9f3), ("58744aa197893a83", L6.Certs.C58744aa197893a83), ("5a94e6f179d11010", L6.Certs.C5a94e6f179d11010), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("724a7accb412014a", L6.Certs.C724a7accb412014a), ("83e997a1e6f21d99", L6.Certs.C83e997a1e6f21d99), ("a0269f9ead157d0c", L6.Certs.Ca0269f9ead157d0c), ("a211ae61440c695c", L6.Certs.Ca211ae61440c695c), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a70957032f7223f5", L6.Certs.Ca70957032f7223f5), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("abe3d270a8beabac", L6.Certs.Cabe3d270a8beabac), ("c283f4873b50bcb4", L6.Certs.Cc283f4873b50bcb4), ("c5e28c7729b266fb", L6.Certs.Cc5e28c7729b266fb), ("cea573f3b40c98b7", L6.Certs.Ccea573f3b40c98b7), ("da286d98e1816635", L6.Certs.Cda286d98e1816635), ("e124815fb09044d8", L6.Certs.Ce124815fb09044d8), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("e80b80e4cb5ae9fe", L6.Certs.Ce80b80e4cb5ae9fe), ("fab0e5212c8d3c79", L6.Certs.Cfab0e5212c8d3c79)]
    22500 24000 { single := 1195, core1 := 305, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
