import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 676–741 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S15

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (10496, 98, [4378744334592])
def s1 : Nat × Nat × List Nat := (272640, 46, [4396999256320])
def s2 : Nat × Nat × List Nat := (534784, 48, [343669221632, 380176443648])
def s3 : Nat × Nat × List Nat := (796928, 43, [])
def s4 : Nat × Nat × List Nat := (76032, 58, [3709946898688, 4379012835584, 4396982282496])
def s5 : Nat × Nat × List Nat := (141568, 58, [])
def s6 : Nat × Nat × List Nat := (665856, 38, [1168303073536, 1204810295552, 1443180980480, 1479688202496])
def s7 : Nat × Nat × List Nat := (207104, 51, [])
def s8 : Nat × Nat × List Nat := (26880, 55, [4396999010560])
def s9 : Nat × Nat × List Nat := (289024, 37, [4329335712000, 4378744613120, 4384097593600, 4396999272704])
def s10 : Nat × Nat × List Nat := (43264, 58, [])
def s11 : Nat × Nat × List Nat := (108800, 33, [4397007481088, 4397108144384, 4397141698816])
def s12 : Nat × Nat × List Nat := (59648, 50, [4329796856064, 4396992751872, 4397001140480, 4397024209152])
def s13 : Nat × Nat × List Nat := (14592, 75, [4397806401792])
def s14 : Nat × Nat × List Nat := (276736, 37, [])
def s15 : Nat × Nat × List Nat := (538880, 37, [])
def s16 : Nat × Nat × List Nat := (80128, 45, [4396987529472, 4397522303232, 4397789690112])
def s17 : Nat × Nat × List Nat := (145664, 44, [])
def s18 : Nat × Nat × List Nat := (669952, 30, [])
def s19 : Nat × Nat × List Nat := (30976, 44, [])
def s20 : Nat × Nat × List Nat := (293120, 30, [])
def s21 : Nat × Nat × List Nat := (47360, 45, [4397024196864, 4397291583744, 4397798045952])
def s22 : Nat × Nat × List Nat := (112896, 27, [4396985465088, 4396987562240, 4397023213824, 4397024262400, 4397174208768, 4397781334272])
def s23 : Nat × Nat × List Nat := (3328, 147, [3473935616, 19847449856, 49643785472, 50718575872, 67092090112, 68166880512])
def s24 : Nat × Nat × List Nat := (265472, 67, [66823916800, 67898707200])
def s25 : Nat × Nat × List Nat := (527616, 63, [68486171904, 4329359019264, 4397253266688])
def s26 : Nat × Nat × List Nat := (68864, 93, [19579079936, 20653870336, 66823720192, 67898510592])
def s27 : Nat × Nat × List Nat := (134400, 87, [68586441984, 4329358626048, 4397252873472])
def s28 : Nat × Nat × List Nat := (986368, 52, [72289536, 3240037632, 3290369280, 3491695872, 4280225024, 31144742144, 32213241088, 32284544256, 35439709440, 35506818304, 36512402688, 36524985600, 36579511552, 36776643840, 37587193088, 37599776000, 37654301952, 37851434240, 64496798976, 65571589376, 66577173760, 66589756672, 66640088320, 66644282624, 66841414912, 67629944064, 67647769856, 67651964160, 67664547072, 67714878720, 67719073024, 67916205312, 68704734464, 2299958070528])
def s29 : Nat × Nat × List Nat := (19712, 86, [18506337536, 19579030784, 20653821184, 66823671040, 67898461440])
def s30 : Nat × Nat × List Nat := (281856, 67, [251940096, 3474214144, 18506599680, 19579292928, 20654083328, 48571370752, 49644064000, 50718854400, 64676449536, 65751239936, 66823933184, 67898723584])
def s31 : Nat × Nat × List Nat := (36096, 82, [4397277940992, 4397378604288])
def s32 : Nat × Nat × List Nat := (52480, 68, [])
def s33 : Nat × Nat × List Nat := (118016, 50, [])
def s34 : Nat × Nat × List Nat := (7424, 82, [3741326592, 3742375168, 19580067072, 19848502528, 20653808896, 20921195776, 20922244352, 49913273600, 50987015424, 67093142784, 67897400576, 67898449152, 68165836032, 68166884608])
def s35 : Nat × Nat × List Nat := (269568, 43, [3473153280, 67897662720])
def s36 : Nat × Nat × List Nat := (531712, 40, [68485127424, 4396984835328, 4396987981056, 4397004758272])
def s37 : Nat × Nat × List Nat := (72960, 54, [3472956672, 20652825856, 67897466112])
def s38 : Nat × Nat × List Nat := (138496, 50, [68585397504, 4396984442112, 4396987587840, 4397004365056])
def s39 : Nat × Nat × List Nat := (990464, 30, [6233344, 3222215936, 3293519104, 3491699968, 4279180544, 31144746240, 31210806528, 32218488064, 32482729216, 33286987008, 33358290176, 33556471040, 35438664960, 35439713536, 35505773824, 36509261056, 36513455360, 36777696512, 37583002880, 37586148608, 37587197184, 37598731520, 37653257472, 37851438336, 65570544896, 66842467584, 67647773952, 67650919680, 67651968256, 67663502592, 67713834240, 67718028544, 67915160832, 67916209408, 68703689984])
def s40 : Nat × Nat × List Nat := (23808, 48, [252730624, 18505293056, 18506341632, 19580083456, 20652776704, 20653825280, 48570064128, 48571112704, 49644854528, 67897416960, 67898465536])
def s41 : Nat × Nat × List Nat := (285952, 34, [18505555200, 20653038848, 65750195456, 67897679104])
def s42 : Nat × Nat × List Nat := (40192, 45, [4397009509632, 4397110172928, 4397226564864])
def s43 : Nat × Nat × List Nat := (56576, 41, [])
def s44 : Nat × Nat × List Nat := (122112, 27, [])
def s45 : Nat × Nat × List Nat := (11520, 82, [1217874898176])
def s46 : Nat × Nat × List Nat := (273664, 39, [])
def s47 : Nat × Nat × List Nat := (535808, 39, [4329359027456])
def s48 : Nat × Nat × List Nat := (77056, 51, [])
def s49 : Nat × Nat × List Nat := (142592, 50, [])
def s50 : Nat × Nat × List Nat := (994560, 28, [4396983201024])
def s51 : Nat × Nat × List Nat := (27904, 44, [])
def s52 : Nat × Nat × List Nat := (290048, 30, [])
def s53 : Nat × Nat × List Nat := (44288, 44, [])
def s54 : Nat × Nat × List Nat := (60672, 39, [4397007432960, 4397108096256])
def s55 : Nat × Nat × List Nat := (126208, 25, [4329360715008, 4329461378304, 4329463475456, 4397007498496, 4397108161792])
def s56 : Nat × Nat × List Nat := (15616, 63, [])
def s57 : Nat × Nat × List Nat := (277760, 33, [])
def s58 : Nat × Nat × List Nat := (539904, 32, [4396982746368, 4397250133248])
def s59 : Nat × Nat × List Nat := (81152, 41, [])
def s60 : Nat × Nat × List Nat := (146688, 39, [4396982353152, 4397249740032])
def s61 : Nat × Nat × List Nat := (32000, 37, [])
def s62 : Nat × Nat × List Nat := (294144, 27, [])
def s63 : Nat × Nat × List Nat := (48384, 36, [4397007420672, 4397108083968, 4397274807552, 4397375470848])
def s64 : Nat × Nat × List Nat := (512, 378, [722629296640, 725866250752, 726941041152, 739002810880, 740077601280, 743314555392, 744389345792])
def s65 : Nat × Nat × List Nat := (262656, 177, [4048548004352])

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
theorem ok54 : shardOK 10 s54.1 s54.2.1 s54.2.2 = true := by decide +kernel
theorem ok55 : shardOK 10 s55.1 s55.2.1 s55.2.2 = true := by decide +kernel
theorem ok56 : shardOK 10 s56.1 s56.2.1 s56.2.2 = true := by decide +kernel
theorem ok57 : shardOK 10 s57.1 s57.2.1 s57.2.2 = true := by decide +kernel
theorem ok58 : shardOK 10 s58.1 s58.2.1 s58.2.2 = true := by decide +kernel
theorem ok59 : shardOK 10 s59.1 s59.2.1 s59.2.2 = true := by decide +kernel
theorem ok60 : shardOK 10 s60.1 s60.2.1 s60.2.2 = true := by decide +kernel
theorem ok61 : shardOK 10 s61.1 s61.2.1 s61.2.2 = true := by decide +kernel
theorem ok62 : shardOK 10 s62.1 s62.2.1 s62.2.2 = true := by decide +kernel
theorem ok63 : shardOK 10 s63.1 s63.2.1 s63.2.2 = true := by decide +kernel
theorem ok64 : shardOK 10 s64.1 s64.2.1 s64.2.2 = true := by decide +kernel
theorem ok65 : shardOK 10 s65.1 s65.2.1 s65.2.2 = true := by decide +kernel

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44, ok45, ok46, ok47, ok48, ok49, ok50, ok51, ok52, ok53, ok54, ok55, ok56, ok57, ok58, ok59, ok60, ok61, ok62, ok63, ok64, ok65]

end L6CheckK.F1.Shards.S15
