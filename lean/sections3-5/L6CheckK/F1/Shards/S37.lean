import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 2019–2093 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S37

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (5504, 49, [])
def s1 : Nat × Nat × List Nat := (136576, 33, [4396982343040, 4397249729920, 4397250778496])
def s2 : Nat × Nat × List Nat := (38272, 33, [4397007410560, 4397274797440, 4397275846016])
def s3 : Nat × Nat × List Nat := (9600, 45, [])
def s4 : Nat × Nat × List Nat := (533888, 28, [21505408, 88614272, 36524533120, 36528727424, 36595836288, 38659433856, 38676211072, 38743319936, 1168252609920, 1168319718784, 1204755637632, 1204759831936, 1204826940800, 1206890538368, 1206907315584, 1206974424448])
def s5 : Nat × Nat × List Nat := (13696, 37, [])
def s6 : Nat × Nat × List Nat := (2432, 76, [])
def s7 : Nat × Nat × List Nat := (264576, 28, [])
def s8 : Nat × Nat × List Nat := (526720, 31, [])
def s9 : Nat × Nat × List Nat := (788864, 25, [])
def s10 : Nat × Nat × List Nat := (67968, 46, [4397519145344])
def s11 : Nat × Nat × List Nat := (133504, 48, [1168302541184, 1204809763200])
def s12 : Nat × Nat × List Nat := (657792, 31, [])
def s13 : Nat × Nat × List Nat := (199040, 37, [])
def s14 : Nat × Nat × List Nat := (18816, 45, [])
def s15 : Nat × Nat × List Nat := (280960, 28, [35932544, 170150272, 19363285376, 19497503104, 2267776567680, 2267778664832, 2267912882560, 2287103920512, 2287106017664, 2287240235392, 2473903540608, 2473937095040, 2474071312768, 2493230893440, 2493264447872, 2493398665600])
def s16 : Nat × Nat × List Nat := (35200, 49, [])
def s17 : Nat × Nat × List Nat := (100736, 33, [4396982307200, 4397510789504, 4397519178112])
def s18 : Nat × Nat × List Nat := (51584, 37, [])
def s19 : Nat × Nat × List Nat := (6528, 46, [4397534812544])
def s20 : Nat × Nat × List Nat := (39296, 33, [4396997974400, 4397526456704, 4397534845312])
def s21 : Nat × Nat × List Nat := (10624, 48, [1374460848512, 1410968070528])
def s22 : Nat × Nat × List Nat := (534912, 31, [])
def s23 : Nat × Nat × List Nat := (141696, 38, [71444864, 36578666880, 1168302549376, 1204809771392, 1374460979584, 1410968201600])
def s24 : Nat × Nat × List Nat := (665984, 31, [71969152, 36579191168, 1168303073664, 1204810295680, 1374461503872, 1410968725888])
def s25 : Nat × Nat × List Nat := (14720, 37, [])
def s26 : Nat × Nat × List Nat := (3456, 63, [67950873984, 4329893268864, 4397787516288])
def s27 : Nat × Nat × List Nat := (265600, 25, [])
def s28 : Nat × Nat × List Nat := (527744, 25, [])
def s29 : Nat × Nat × List Nat := (68992, 43, [])
def s30 : Nat × Nat × List Nat := (134528, 43, [])
def s31 : Nat × Nat × List Nat := (986496, 21, [4396983192960])
def s32 : Nat × Nat × List Nat := (19840, 39, [67950890368])
def s33 : Nat × Nat × List Nat := (281984, 25, [])
def s34 : Nat × Nat × List Nat := (36224, 40, [4329356430720, 4397244386688, 4397277941120, 4397779160448])
def s35 : Nat × Nat × List Nat := (52608, 32, [4396982259072, 4397510741376])
def s36 : Nat × Nat × List Nat := (118144, 25, [4329335541120, 4329864023424, 4329866120576, 4396982324608, 4397510806912])
def s37 : Nat × Nat × List Nat := (7552, 40, [67682442624, 4397522230656, 4397539007872, 4397786471808])
def s38 : Nat × Nat × List Nat := (40320, 27, [4396975955328, 4396985392512, 4397002169728, 4397009509760, 4397224467840, 4397778115968])
def s39 : Nat × Nat × List Nat := (11648, 39, [4329893277056])
def s40 : Nat × Nat × List Nat := (535936, 25, [])
def s41 : Nat × Nat × List Nat := (15744, 32, [4396982222208, 4397249609088])
def s42 : Nat × Nat × List Nat := (146816, 25, [67646930304, 67914317184, 67918511488, 4396982353280, 4397249740160])
def s43 : Nat × Nat × List Nat := (640, 192, [794585727616, 807722287744, 812034032256])
def s44 : Nat × Nat × List Nat := (262784, 76, [])
def s45 : Nat × Nat × List Nat := (524928, 92, [1894097879680])
def s46 : Nat × Nat × List Nat := (787072, 67, [4055456547456, 4330368008832])
def s47 : Nat × Nat × List Nat := (66176, 106, [295764608, 429982336, 21485388416, 21619606144, 21770601088, 21904818816, 618771055232, 618903175808, 618905272960, 639960679040, 640092799616, 640094896768, 640245891712, 640378012288, 640380109440, 687490531968, 687616361088, 687624749696, 708680155776, 708805984896, 708814373504, 708965368448, 709091197568, 709099586176, 756199522944, 756335837824, 756342129280, 777389146752, 777525461632, 777531753088, 777674359424, 777810674304, 777816965760, 794854228608, 807739130496, 811765662336, 812017320576, 812034097792, 2289226023552, 2289228120704, 2289362338432, 2357939208832, 2357947597440, 2358081815168, 2770398675584, 2839116055168, 2839118152320, 2907829240448, 2907837629056, 2976414499456, 2976420790912, 2976422888064, 2976546620032, 2976548717184, 2976555008640, 2976557105792])
def s48 : Nat × Nat × List Nat := (328320, 45, [])
def s49 : Nat × Nat × List Nat := (590464, 48, [])
def s50 : Nat × Nat × List Nat := (852608, 42, [])
def s51 : Nat × Nat × List Nat := (131712, 106, [])
def s52 : Nat × Nat × List Nat := (393856, 49, [])
def s53 : Nat × Nat × List Nat := (656000, 58, [])
def s54 : Nat × Nat × List Nat := (918144, 47, [4330334585472])
def s55 : Nat × Nat × List Nat := (197248, 81, [866321024, 1000538752, 619339514496, 619341611648, 619473732224, 619475829376, 688052699776, 688061088384, 688186917504, 688195306112, 756770079360, 756772176512, 756778467968, 756904297088, 756906394240, 756912685696, 3642996490880, 3642998588032, 3643132805760, 3711709676160, 3711718064768, 3711852282496, 4124169142912, 4192886522496, 4192888619648, 4261599707776, 4261608096384, 4330184966784, 4330191258240, 4330193355392, 4330317087360, 4330319184512, 4330325475968, 4330327573120])
def s56 : Nat × Nat × List Nat := (459392, 37, [])
def s57 : Nat × Nat × List Nat := (721536, 41, [756770603648, 4330183393920])
def s58 : Nat × Nat × List Nat := (17024, 100, [])
def s59 : Nat × Nat × List Nat := (82560, 55, [])
def s60 : Nat × Nat × List Nat := (148096, 58, [])
def s61 : Nat × Nat × List Nat := (213632, 44, [])
def s62 : Nat × Nat × List Nat := (33408, 116, [1206902620800, 1894097388160])
def s63 : Nat × Nat × List Nat := (557696, 92, [657147331200, 794586284672, 1756658958976, 1894097912448])
def s64 : Nat × Nat × List Nat := (98944, 58, [])
def s65 : Nat × Nat × List Nat := (623232, 38, [618761126528, 657415832192, 756200080000, 794854785664])
def s66 : Nat × Nat × List Nat := (164480, 67, [])
def s67 : Nat × Nat × List Nat := (688768, 49, [])
def s68 : Nat × Nat × List Nat := (230016, 48, [857965184, 619331158656, 619333255808, 688052732544, 756770112128, 756772209280, 3642988135040, 3642990232192, 3711709708928, 4330182902400, 4330184999552])
def s69 : Nat × Nat × List Nat := (754304, 34, [619331682944, 756770636416, 4192744473216, 4330183426688])
def s70 : Nat × Nat × List Nat := (49792, 86, [344448877184, 619293229696, 894204691072, 4055267066496, 4330178527872])
def s71 : Nat × Nat × List Nat := (115328, 50, [])
def s72 : Nat × Nat × List Nat := (180864, 54, [344415453824, 894171267712, 4330145104512])
def s73 : Nat × Nat × List Nat := (4736, 100, [])
def s74 : Nat × Nat × List Nat := (70272, 55, [])

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
theorem ok66 : shardOK 10 s66.1 s66.2.1 s66.2.2 = true := by decide +kernel
theorem ok67 : shardOK 10 s67.1 s67.2.1 s67.2.2 = true := by decide +kernel
theorem ok68 : shardOK 10 s68.1 s68.2.1 s68.2.2 = true := by decide +kernel
theorem ok69 : shardOK 10 s69.1 s69.2.1 s69.2.2 = true := by decide +kernel
theorem ok70 : shardOK 10 s70.1 s70.2.1 s70.2.2 = true := by decide +kernel
theorem ok71 : shardOK 10 s71.1 s71.2.1 s71.2.2 = true := by decide +kernel
theorem ok72 : shardOK 10 s72.1 s72.2.1 s72.2.2 = true := by decide +kernel
theorem ok73 : shardOK 10 s73.1 s73.2.1 s73.2.2 = true := by decide +kernel
theorem ok74 : shardOK 10 s74.1 s74.2.1 s74.2.2 = true := by decide +kernel

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, s72, s73, s74]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44, ok45, ok46, ok47, ok48, ok49, ok50, ok51, ok52, ok53, ok54, ok55, ok56, ok57, ok58, ok59, ok60, ok61, ok62, ok63, ok64, ok65, ok66, ok67, ok68, ok69, ok70, ok71, ok72, ok73, ok74]

end L6CheckK.F1.Shards.S37
