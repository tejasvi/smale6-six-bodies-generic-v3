import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C30
import L6Check.F34.Data.Common
import L6Check.F34.Data.C30
import L6Check.Certs.C019a393029b80aea
import L6Check.Certs.C04a16343360b0bfd
import L6Check.Certs.C06bbb164f0e1f35e
import L6Check.Certs.C163dffdaeaa03236
import L6Check.Certs.C16ee5990016ab542
import L6Check.Certs.C1ea0fbd8e9193842
import L6Check.Certs.C20df3cfcdcd1f663
import L6Check.Certs.C2c251e1864d74f35
import L6Check.Certs.C2db21cc247a6c18f
import L6Check.Certs.C2ed148ab9a0bbfb9
import L6Check.Certs.C3070a790268f073d
import L6Check.Certs.C32ecb894aac76283
import L6Check.Certs.C34f4fb0eb0614490
import L6Check.Certs.C3a04360bbae948f5
import L6Check.Certs.C3c664902aaacbd87
import L6Check.Certs.C41360c3300ac062f
import L6Check.Certs.C434f4ada476c6542
import L6Check.Certs.C44f6f0a132715eda
import L6Check.Certs.C462d5f0922a88aa6
import L6Check.Certs.C463084c7a89ea757
import L6Check.Certs.C46b92bfd7fbd4f86
import L6Check.Certs.C4c0b9182bad49321
import L6Check.Certs.C4dc3233be7a467c0
import L6Check.Certs.C56e4849a55cd0392
import L6Check.Certs.C59e0304641b0fd0e
import L6Check.Certs.C66033b25891a3b95
import L6Check.Certs.C6d2bce990d0e417f
import L6Check.Certs.C70b66bcddfce894b
import L6Check.Certs.C70fdcbcc7928a3a7
import L6Check.Certs.C71badf5c5e3ec565
import L6Check.Certs.C77c9b982806b4b3b
import L6Check.Certs.C77d101386f0c2df1
import L6Check.Certs.C7eee4283cce65efa
import L6Check.Certs.C7ffb964a4f33310a
import L6Check.Certs.C83560ff750ff3220
import L6Check.Certs.C89ae6b12c4314316
import L6Check.Certs.C8b4dd8bd8d0ecb1f
import L6Check.Certs.C998d48980a3d49fc
import L6Check.Certs.C99df23d612725910
import L6Check.Certs.C9a5bb2605cc2eb84
import L6Check.Certs.Ca148e06aabcb183f
import L6Check.Certs.Ca1ff788c88be1bed
import L6Check.Certs.Cab140b54680ace8a
import L6Check.Certs.Cacb2172747090cad
import L6Check.Certs.Cae87e69807b8692e
import L6Check.Certs.Cb42c2022945b5f78
import L6Check.Certs.Cb43c9356a45fc942
import L6Check.Certs.Cb58d0853c0193779
import L6Check.Certs.Cb7d19dd1e1382c3f
import L6Check.Certs.Cbf2609a02bd00f4a
import L6Check.Certs.Cc1ed1134280e5006
import L6Check.Certs.Cc36c9d9d9956b9ba
import L6Check.Certs.Cc49c5d3f244af555
import L6Check.Certs.Cc530190de45d75b1
import L6Check.Certs.Cd09943b8475b721e
import L6Check.Certs.Cd4d1f5d0a8df413d
import L6Check.Certs.Cd63e35e560d65061
import L6Check.Certs.Cd68cff27d2d3ff6d
import L6Check.Certs.Cd961b8a0cfc19ad2
import L6Check.Certs.Cdaed7b3ec3207add
import L6Check.Certs.Cdef56078d1e24253
import L6Check.Certs.Cdf02b8cabed0cb47
import L6Check.Certs.Ce1e9156562b4ba25
import L6Check.Certs.Ce3154be42fd020c7
import L6Check.Certs.Ce46c9f890e99b7af
import L6Check.Certs.Cecb8e166ae26d322
import L6Check.Certs.Cf22c022637e274a0
import L6Check.Certs.Cfafc3cdcdaca97ae
import L6Check.Certs.Cfc9b3c24ba5075a8

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 30, cells 0 ≤ cell < 273 of
`data/cells/c30.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 273` of class 30 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 14, core1 := 198, core2 := 61, opn := 0 }. -/
theorem F34S_c30_k0 : checkChunkS 30 (L6.F2.diagOf 30) L6.F2.Data.cells_c30 single_30 links_30 pass_30 open43
    [("019a393029b80aea", L6.Certs.C019a393029b80aea), ("04a16343360b0bfd", L6.Certs.C04a16343360b0bfd), ("06bbb164f0e1f35e", L6.Certs.C06bbb164f0e1f35e), ("163dffdaeaa03236", L6.Certs.C163dffdaeaa03236), ("16ee5990016ab542", L6.Certs.C16ee5990016ab542), ("1ea0fbd8e9193842", L6.Certs.C1ea0fbd8e9193842), ("20df3cfcdcd1f663", L6.Certs.C20df3cfcdcd1f663), ("2c251e1864d74f35", L6.Certs.C2c251e1864d74f35), ("2db21cc247a6c18f", L6.Certs.C2db21cc247a6c18f), ("2ed148ab9a0bbfb9", L6.Certs.C2ed148ab9a0bbfb9), ("3070a790268f073d", L6.Certs.C3070a790268f073d), ("32ecb894aac76283", L6.Certs.C32ecb894aac76283), ("34f4fb0eb0614490", L6.Certs.C34f4fb0eb0614490), ("3a04360bbae948f5", L6.Certs.C3a04360bbae948f5), ("3c664902aaacbd87", L6.Certs.C3c664902aaacbd87), ("41360c3300ac062f", L6.Certs.C41360c3300ac062f), ("434f4ada476c6542", L6.Certs.C434f4ada476c6542), ("44f6f0a132715eda", L6.Certs.C44f6f0a132715eda), ("462d5f0922a88aa6", L6.Certs.C462d5f0922a88aa6), ("463084c7a89ea757", L6.Certs.C463084c7a89ea757), ("46b92bfd7fbd4f86", L6.Certs.C46b92bfd7fbd4f86), ("4c0b9182bad49321", L6.Certs.C4c0b9182bad49321), ("4dc3233be7a467c0", L6.Certs.C4dc3233be7a467c0), ("56e4849a55cd0392", L6.Certs.C56e4849a55cd0392), ("59e0304641b0fd0e", L6.Certs.C59e0304641b0fd0e), ("66033b25891a3b95", L6.Certs.C66033b25891a3b95), ("6d2bce990d0e417f", L6.Certs.C6d2bce990d0e417f), ("70b66bcddfce894b", L6.Certs.C70b66bcddfce894b), ("70fdcbcc7928a3a7", L6.Certs.C70fdcbcc7928a3a7), ("71badf5c5e3ec565", L6.Certs.C71badf5c5e3ec565), ("77c9b982806b4b3b", L6.Certs.C77c9b982806b4b3b), ("77d101386f0c2df1", L6.Certs.C77d101386f0c2df1), ("7eee4283cce65efa", L6.Certs.C7eee4283cce65efa), ("7ffb964a4f33310a", L6.Certs.C7ffb964a4f33310a), ("83560ff750ff3220", L6.Certs.C83560ff750ff3220), ("89ae6b12c4314316", L6.Certs.C89ae6b12c4314316), ("8b4dd8bd8d0ecb1f", L6.Certs.C8b4dd8bd8d0ecb1f), ("998d48980a3d49fc", L6.Certs.C998d48980a3d49fc), ("99df23d612725910", L6.Certs.C99df23d612725910), ("9a5bb2605cc2eb84", L6.Certs.C9a5bb2605cc2eb84), ("a148e06aabcb183f", L6.Certs.Ca148e06aabcb183f), ("a1ff788c88be1bed", L6.Certs.Ca1ff788c88be1bed), ("ab140b54680ace8a", L6.Certs.Cab140b54680ace8a), ("acb2172747090cad", L6.Certs.Cacb2172747090cad), ("ae87e69807b8692e", L6.Certs.Cae87e69807b8692e), ("b42c2022945b5f78", L6.Certs.Cb42c2022945b5f78), ("b43c9356a45fc942", L6.Certs.Cb43c9356a45fc942), ("b58d0853c0193779", L6.Certs.Cb58d0853c0193779), ("b7d19dd1e1382c3f", L6.Certs.Cb7d19dd1e1382c3f), ("bf2609a02bd00f4a", L6.Certs.Cbf2609a02bd00f4a), ("c1ed1134280e5006", L6.Certs.Cc1ed1134280e5006), ("c36c9d9d9956b9ba", L6.Certs.Cc36c9d9d9956b9ba), ("c49c5d3f244af555", L6.Certs.Cc49c5d3f244af555), ("c530190de45d75b1", L6.Certs.Cc530190de45d75b1), ("d09943b8475b721e", L6.Certs.Cd09943b8475b721e), ("d4d1f5d0a8df413d", L6.Certs.Cd4d1f5d0a8df413d), ("d63e35e560d65061", L6.Certs.Cd63e35e560d65061), ("d68cff27d2d3ff6d", L6.Certs.Cd68cff27d2d3ff6d), ("d961b8a0cfc19ad2", L6.Certs.Cd961b8a0cfc19ad2), ("daed7b3ec3207add", L6.Certs.Cdaed7b3ec3207add), ("def56078d1e24253", L6.Certs.Cdef56078d1e24253), ("df02b8cabed0cb47", L6.Certs.Cdf02b8cabed0cb47), ("e1e9156562b4ba25", L6.Certs.Ce1e9156562b4ba25), ("e3154be42fd020c7", L6.Certs.Ce3154be42fd020c7), ("e46c9f890e99b7af", L6.Certs.Ce46c9f890e99b7af), ("ecb8e166ae26d322", L6.Certs.Cecb8e166ae26d322), ("f22c022637e274a0", L6.Certs.Cf22c022637e274a0), ("fafc3cdcdaca97ae", L6.Certs.Cfafc3cdcdaca97ae), ("fc9b3c24ba5075a8", L6.Certs.Cfc9b3c24ba5075a8)]
    0 273 { single := 14, core1 := 198, core2 := 61, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
