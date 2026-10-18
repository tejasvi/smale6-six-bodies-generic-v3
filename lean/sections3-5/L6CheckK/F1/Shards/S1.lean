import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 15–44 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S1

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (16384, 378, [2287072198656, 2493262086144, 2561983660032, 2768240656384, 2836962230272, 3043152117760, 3111873691648])
def s1 : Nat × Nat × List Nat := (278528, 192, [2295662395392, 2501852282880, 2570573856768])
def s2 : Nat × Nat × List Nat := (540672, 177, [4048082714624])
def s3 : Nat × Nat × List Nat := (802816, 147, [4229709824, 7466663936, 63284461568, 64359251968, 67596206080, 68670996480])
def s4 : Nat × Nat × List Nat := (81920, 192, [2291367231488, 2772535689216, 2841257263104])
def s5 : Nat × Nat × List Nat := (344064, 92, [2299957428224])
def s6 : Nat × Nat × List Nat := (606208, 76, [])
def s7 : Nat × Nat × List Nat := (868352, 67, [67579494400, 68654284800])
def s8 : Nat × Nat × List Nat := (147456, 177, [3768859115520])
def s9 : Nat × Nat × List Nat := (409600, 76, [])
def s10 : Nat × Nat × List Nat := (671744, 76, [])
def s11 : Nat × Nat × List Nat := (933888, 63, [67832266752, 4329409757184, 4397002014720])
def s12 : Nat × Nat × List Nat := (212992, 147, [4078125056, 11660378112, 58837909504, 59912699904, 67494952960, 68569743360])
def s13 : Nat × Nat × List Nat := (475136, 67, [67428106240, 68502896640])
def s14 : Nat × Nat × List Nat := (737280, 63, [67882401792, 4329359228928, 4397052149760])
def s15 : Nat × Nat × List Nat := (32768, 378, [1272385142784, 1275622096896, 1276696887296, 1279967395840, 1281042186240, 1284279140352, 1285353930752])
def s16 : Nat × Nat × List Nat := (294912, 177, [4048145383424])
def s17 : Nat × Nat × List Nat := (557056, 192, [1822141480960, 1825378435072, 1826453225472])
def s18 : Nat × Nat × List Nat := (819200, 147, [207167979520, 413357867008, 3986737102848, 4055458676736, 4261648564224, 4330370138112])
def s19 : Nat × Nat × List Nat := (98304, 177, [3768871649280])
def s20 : Nat × Nat × List Nat := (360448, 76, [])
def s21 : Nat × Nat × List Nat := (622592, 76, [])
def s22 : Nat × Nat × List Nat := (884736, 63, [67794468864, 4329447456768, 4397014548480])
def s23 : Nat × Nat × List Nat := (163840, 192, [1547263180800, 1554845433856, 1555920224256])
def s24 : Nat × Nat × List Nat := (425984, 76, [])
def s25 : Nat × Nat × List Nat := (688128, 92, [2097019518976])
def s26 : Nat × Nat × List Nat := (950272, 67, [4261615140864, 4330336714752])
def s27 : Nat × Nat × List Nat := (229376, 147, [207016394752, 688184852480, 3711707611136, 3780429185024, 4261597642752, 4330319216640])
def s28 : Nat × Nat × List Nat := (491520, 63, [67693412352, 4329547726848, 4397114818560])
def s29 : Nat × Nat × List Nat := (753664, 67, [4261463949312, 4330185523200])

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
theorem ok15 : shardOK 10 s15.1 s15.2.1 s15.2.2 = true := by decide +kernel
theorem ok16 : shardOK 10 s16.1 s16.2.1 s16.2.2 = true := by decide +kernel
theorem ok17 : shardOK 10 s17.1 s17.2.1 s17.2.2 = true := by decide +kernel
theorem ok18 : shardOK 10 s18.1 s18.2.1 s18.2.2 = true := by decide +kernel
theorem ok19 : shardOK 10 s19.1 s19.2.1 s19.2.2 = true := by decide +kernel
theorem ok20 : shardOK 10 s20.1 s20.2.1 s20.2.2 = true := by decide +kernel
theorem ok21 : shardOK 10 s21.1 s21.2.1 s21.2.2 = true := by decide +kernel
theorem ok22 : shardOK 10 s22.1 s22.2.1 s22.2.2 = true := by decide +kernel
theorem ok23 : shardOK 10 s23.1 s23.2.1 s23.2.2 = true := by decide +kernel
theorem ok24 : shardOK 10 s24.1 s24.2.1 s24.2.2 = true := by decide +kernel
theorem ok25 : shardOK 10 s25.1 s25.2.1 s25.2.2 = true := by decide +kernel
theorem ok26 : shardOK 10 s26.1 s26.2.1 s26.2.2 = true := by decide +kernel
theorem ok27 : shardOK 10 s27.1 s27.2.1 s27.2.2 = true := by decide +kernel
theorem ok28 : shardOK 10 s28.1 s28.2.1 s28.2.2 = true := by decide +kernel
theorem ok29 : shardOK 10 s29.1 s29.2.1 s29.2.2 = true := by decide +kernel

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29]

end L6CheckK.F1.Shards.S1
