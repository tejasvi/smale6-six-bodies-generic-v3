import L6CheckK.F1.All
import L6K.F1.SortR

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The checks of Proposition 3.1 that need all shards or all classes, except the comparison of codes. -/

namespace L6CheckK.F1

open L6F1 L6K.F1

theorem g_prefixes : allShards.map (·.1) = edgesUpTo 6 level := by decide +kernel
theorem g_prefixes_nodup : strictSorted (msortR 20 (allShards.map (·.1))) = true := by decide +kernel
theorem g_sum : (allShards.map (·.2.1)).sum = 932677 := by decide +kernel
theorem g_codes_len : codesAll.length = 82712 := by decide +kernel
theorem g_chain : chainOK 0 ivls = true := by decide +kernel
theorem g_perms : checkPermsK 6 = true := by decide +kernel
theorem g_keys : strictSorted (classes6L.map fun x => rawKey 6 x.1) = true := by decide +kernel
theorem g_len : classes6L.length = 191 := by decide +kernel

end L6CheckK.F1
