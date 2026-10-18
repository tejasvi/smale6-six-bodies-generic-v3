import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 0–14 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S0

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (0, 648, [])
def s1 : Nat × Nat × List Nat := (262144, 378, [2293514895360, 2362240663552, 2430962237440, 2499704782848, 2568426356736, 2637152124928, 2705873698816])
def s2 : Nat × Nat × List Nat := (524288, 378, [1684702494720, 1685779382272, 1686854172672, 1687939448832, 1689014239232, 1690091126784, 1691165917184])
def s3 : Nat × Nat × List Nat := (786432, 297, [1007419392, 62211751936, 63288639488, 64363429888, 65448706048, 66523496448, 67600384000, 68675174400, 3918019690496, 3986745458688, 4055467032576, 4124209577984, 4192931151872, 4261656920064, 4330378493952])
def s4 : Nat × Nat × List Nat := (65536, 378, [2289219731456, 2357945499648, 2426667073536, 2770388189184, 2839109763072, 2907835531264, 2976557105152])
def s5 : Nat × Nat × List Nat := (327680, 192, [2297809928192, 2366535696384, 2435257270272])
def s6 : Nat × Nat × List Nat := (589824, 177, [4187694366720])
def s7 : Nat × Nat × List Nat := (851968, 147, [6377242624, 7454130176, 65431994368, 66506784768, 67583672320, 68658462720])
def s8 : Nat × Nat × List Nat := (131072, 378, [1409824194560, 1410901082112, 1411975872512, 1417406447616, 1418481238016, 1419558125568, 1420632915968])
def s9 : Nat × Nat × List Nat := (393216, 177, [4187744501760])
def s10 : Nat × Nat × List Nat := (655360, 192, [1959580532736, 1960657420288, 1961732210688])
def s11 : Nat × Nat × List Nat := (917504, 147, [344607031296, 413332799488, 4124176154624, 4192897728512, 4261623496704, 4330345070592])
def s12 : Nat × Nat × List Nat := (196608, 297, [855834624, 57765199872, 58842087424, 59916877824, 65347452928, 66422243328, 67499130880, 68573921280, 3642990198784, 3711715966976, 3780437540864, 4124158656512, 4192880230400, 4261605998592, 4330327572480])
def s13 : Nat × Nat × List Nat := (458752, 147, [10520821760, 11597709312, 65280606208, 66355396608, 67432284160, 68507074560])
def s14 : Nat × Nat × List Nat := (720896, 147, [619333746688, 688059514880, 4124024963072, 4192746536960, 4261472305152, 4330193879040])

theorem ok0 : shardOK 10 s0.1 s0.2.1 s0.2.2 = true := by decide +kernel
theorem ok1 : shardOK 10 s1.1 s1.2.1 s1.2.2 = true := by decide +kernel
theorem ok2 : shardOK 10 s2.1 s2.2.1 s2.2.2 = true := by decide +kernel
theorem ok3 : shardOK 10 s3.1 s3.2.1 s3.2.2 = true := by decide +kernel
theorem ok4 : shardOK 10 s4.1 s4.2.1 s4.2.2 = true := by decide +kernel
theorem ok5 : shardOK 10 s5.1 s5.2.1 s5.2.2 = true := by decide +kernel
theorem ok6 : shardOK 10 s6.1 s6.2.1 s6.2.2 = true := by decide +kernel
theorem ok7 : shardOK 10 s7.1 s7.2.1 s7.2.2 = true := by decide +kernel
theorem ok8 : shardOK 10 s8.1 s8.2.1 s8.2.2 = true := by decide +kernel
theorem ok9 : shardOK 10 s9.1 s9.2.1 s9.2.2 = true := by decide +kernel
theorem ok10 : shardOK 10 s10.1 s10.2.1 s10.2.2 = true := by decide +kernel
theorem ok11 : shardOK 10 s11.1 s11.2.1 s11.2.2 = true := by decide +kernel
theorem ok12 : shardOK 10 s12.1 s12.2.1 s12.2.2 = true := by decide +kernel
theorem ok13 : shardOK 10 s13.1 s13.2.1 s13.2.2 = true := by decide +kernel
theorem ok14 : shardOK 10 s14.1 s14.2.1 s14.2.2 = true := by decide +kernel

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14]

end L6CheckK.F1.Shards.S0
