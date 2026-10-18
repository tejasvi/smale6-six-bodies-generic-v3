import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 84–137 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S3

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (36864, 177, [3559460474880])
def s1 : Nat × Nat × List Nat := (299008, 76, [])
def s2 : Nat × Nat × List Nat := (561152, 76, [])
def s3 : Nat × Nat × List Nat := (823296, 63, [67810136064, 4329431666688, 4397030215680])
def s4 : Nat × Nat × List Nat := (102400, 76, [])
def s5 : Nat × Nat × List Nat := (364544, 31, [])
def s6 : Nat × Nat × List Nat := (626688, 28, [])
def s7 : Nat × Nat × List Nat := (888832, 25, [])
def s8 : Nat × Nat × List Nat := (167936, 76, [])
def s9 : Nat × Nat × List Nat := (430080, 28, [])
def s10 : Nat × Nat × List Nat := (692224, 31, [])
def s11 : Nat × Nat × List Nat := (954368, 25, [])
def s12 : Nat × Nat × List Nat := (233472, 63, [67759214592, 4329481408512, 4397180620800])
def s13 : Nat × Nat × List Nat := (495616, 25, [])
def s14 : Nat × Nat × List Nat := (757760, 25, [])
def s15 : Nat × Nat × List Nat := (53248, 147, [6203428864, 10548727808, 55578775552, 59890520064, 64235819008, 68547563520])
def s16 : Nat × Nat × List Nat := (315392, 67, [64168972288, 68480716800])
def s17 : Nat × Nat × List Nat := (577536, 63, [67872804864, 4329368506368, 4397092884480])
def s18 : Nat × Nat × List Nat := (118784, 67, [59873808384, 68530851840])
def s19 : Nat × Nat × List Nat := (380928, 29, [68464005120])
def s20 : Nat × Nat × List Nat := (643072, 25, [])
def s21 : Nat × Nat × List Nat := (184320, 63, [67771748352, 4329468776448, 4397193154560])
def s22 : Nat × Nat × List Nat := (446464, 25, [])
def s23 : Nat × Nat × List Nat := (708608, 25, [])
def s24 : Nat × Nat × List Nat := (8192, 378, [1204742529024, 1206902595584, 1209054273536, 1211247894528, 1213399572480, 1215559639040, 1217711316992])
def s25 : Nat × Nat × List Nat := (270336, 177, [3978348994560])
def s26 : Nat × Nat × List Nat := (532480, 192, [1754498867200, 1756658933760, 1758810611712])
def s27 : Nat × Nat × List Nat := (794624, 147, [207174246400, 344638365696, 3918017601536, 4055464943616, 4192929062912, 4330376404992])
def s28 : Nat × Nat × List Nat := (73728, 177, [3699075260416])
def s29 : Nat × Nat × List Nat := (335872, 76, [])
def s30 : Nat × Nat × List Nat := (598016, 76, [])
def s31 : Nat × Nat × List Nat := (860160, 63, [67788152832, 4329453723648, 4397020815360])
def s32 : Nat × Nat × List Nat := (139264, 192, [1479620567040, 1486125932544, 1488277610496])
def s33 : Nat × Nat × List Nat := (401408, 76, [])
def s34 : Nat × Nat × List Nat := (663552, 92, [2029376905216])
def s35 : Nat × Nat × List Nat := (925696, 67, [4192895639552, 4330342981632])
def s36 : Nat × Nat × List Nat := (204800, 147, [207022661632, 619465351168, 3642988109824, 3780435451904, 4192878141440, 4330325483520])
def s37 : Nat × Nat × List Nat := (466944, 63, [67687096320, 4329553993728, 4397121085440])
def s38 : Nat × Nat × List Nat := (729088, 67, [4192744448000, 4330191790080])
def s39 : Nat × Nat × List Nat := (24576, 177, [3559463608320])
def s40 : Nat × Nat × List Nat := (286720, 76, [])
def s41 : Nat × Nat × List Nat := (548864, 76, [])
def s42 : Nat × Nat × List Nat := (811008, 63, [67800686592, 4329441091584, 4397033349120])
def s43 : Nat × Nat × List Nat := (90112, 76, [])
def s44 : Nat × Nat × List Nat := (352256, 31, [])
def s45 : Nat × Nat × List Nat := (614400, 28, [])
def s46 : Nat × Nat × List Nat := (876544, 25, [])
def s47 : Nat × Nat × List Nat := (155648, 76, [])
def s48 : Nat × Nat × List Nat := (417792, 28, [])
def s49 : Nat × Nat × List Nat := (679936, 31, [])
def s50 : Nat × Nat × List Nat := (942080, 25, [])
def s51 : Nat × Nat × List Nat := (221184, 63, [67749765120, 4329490833408, 4397183754240])
def s52 : Nat × Nat × List Nat := (483328, 25, [])
def s53 : Nat × Nat × List Nat := (745472, 25, [])

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
theorem ok30 : shardOK 10 s30.1 s30.2.1 s30.2.2 = true := by decide +kernel
theorem ok31 : shardOK 10 s31.1 s31.2.1 s31.2.2 = true := by decide +kernel
theorem ok32 : shardOK 10 s32.1 s32.2.1 s32.2.2 = true := by decide +kernel
theorem ok33 : shardOK 10 s33.1 s33.2.1 s33.2.2 = true := by decide +kernel
theorem ok34 : shardOK 10 s34.1 s34.2.1 s34.2.2 = true := by decide +kernel
theorem ok35 : shardOK 10 s35.1 s35.2.1 s35.2.2 = true := by decide +kernel
theorem ok36 : shardOK 10 s36.1 s36.2.1 s36.2.2 = true := by decide +kernel
theorem ok37 : shardOK 10 s37.1 s37.2.1 s37.2.2 = true := by decide +kernel
theorem ok38 : shardOK 10 s38.1 s38.2.1 s38.2.2 = true := by decide +kernel
theorem ok39 : shardOK 10 s39.1 s39.2.1 s39.2.2 = true := by decide +kernel
theorem ok40 : shardOK 10 s40.1 s40.2.1 s40.2.2 = true := by decide +kernel
theorem ok41 : shardOK 10 s41.1 s41.2.1 s41.2.2 = true := by decide +kernel
theorem ok42 : shardOK 10 s42.1 s42.2.1 s42.2.2 = true := by decide +kernel
theorem ok43 : shardOK 10 s43.1 s43.2.1 s43.2.2 = true := by decide +kernel
theorem ok44 : shardOK 10 s44.1 s44.2.1 s44.2.2 = true := by decide +kernel
theorem ok45 : shardOK 10 s45.1 s45.2.1 s45.2.2 = true := by decide +kernel
theorem ok46 : shardOK 10 s46.1 s46.2.1 s46.2.2 = true := by decide +kernel
theorem ok47 : shardOK 10 s47.1 s47.2.1 s47.2.2 = true := by decide +kernel
theorem ok48 : shardOK 10 s48.1 s48.2.1 s48.2.2 = true := by decide +kernel
theorem ok49 : shardOK 10 s49.1 s49.2.1 s49.2.2 = true := by decide +kernel
theorem ok50 : shardOK 10 s50.1 s50.2.1 s50.2.2 = true := by decide +kernel
theorem ok51 : shardOK 10 s51.1 s51.2.1 s51.2.2 = true := by decide +kernel
theorem ok52 : shardOK 10 s52.1 s52.2.1 s52.2.2 = true := by decide +kernel
theorem ok53 : shardOK 10 s53.1 s53.2.1 s53.2.2 = true := by decide +kernel

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44, ok45, ok46, ok47, ok48, ok49, ok50, ok51, ok52, ok53]

end L6CheckK.F1.Shards.S3
