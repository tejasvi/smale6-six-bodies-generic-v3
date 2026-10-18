import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 8384–8463 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S129

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (41608, 49, [])
def s1 : Nat × Nat × List Nat := (565896, 49, [])
def s2 : Nat × Nat × List Nat := (172680, 42, [])
def s3 : Nat × Nat × List Nat := (696968, 42, [])
def s4 : Nat × Nat × List Nat := (12936, 43, [413125325448, 4330135499400])
def s5 : Nat × Nat × List Nat := (2696, 92, [739002813064, 807722289800, 1013880720008, 1082600196744])
def s6 : Nat × Nat × List Nat := (264840, 31, [])
def s7 : Nat × Nat × List Nat := (526984, 42, [])
def s8 : Nat × Nat × List Nat := (789128, 29, [3986737072776, 4055456549512, 4261614979720, 4330334456456])
def s9 : Nat × Nat × List Nat := (68232, 38, [687480048264, 739019655816, 756199525000, 807739132552])
def s10 : Nat × Nat × List Nat := (133768, 49, [])
def s11 : Nat × Nat × List Nat := (658056, 42, [])
def s12 : Nat × Nat × List Nat := (199304, 34, [688050604680, 756770081416, 4261463394952, 4330182871688])
def s13 : Nat × Nat × List Nat := (19080, 48, [])
def s14 : Nat × Nat × List Nat := (35464, 58, [])
def s15 : Nat × Nat × List Nat := (559752, 42, [])
def s16 : Nat × Nat × List Nat := (166536, 42, [])
def s17 : Nat × Nat × List Nat := (690824, 42, [])
def s18 : Nat × Nat × List Nat := (51848, 41, [817941128, 344415324808, 619293231752, 825451661960, 894171138696, 3986547591816, 4055267068552, 4261425498760, 4330144975496])
def s19 : Nat × Nat × List Nat := (6792, 38, [687464258184, 739003865736, 962342165128, 1013881772680])
def s20 : Nat × Nat × List Nat := (10888, 49, [])
def s21 : Nat × Nat × List Nat := (535176, 42, [])
def s22 : Nat × Nat × List Nat := (141960, 49, [])
def s23 : Nat × Nat × List Nat := (666248, 42, [])
def s24 : Nat × Nat × List Nat := (43656, 42, [])
def s25 : Nat × Nat × List Nat := (567944, 42, [])
def s26 : Nat × Nat × List Nat := (174728, 42, [])
def s27 : Nat × Nat × List Nat := (699016, 42, [])
def s28 : Nat × Nat × List Nat := (14984, 34, [688003234440, 962881141384, 4055257594504, 4330135501448])
def s29 : Nat × Nat × List Nat := (904, 86, [343811294088, 1375140316040, 1443859792776, 3230029317000, 4330077815688])
def s30 : Nat × Nat × List Nat := (263048, 39, [4330170352520])
def s31 : Nat × Nat × List Nat := (525192, 43, [1374603969416, 4329541469064])
def s32 : Nat × Nat × List Nat := (66440, 44, [])
def s33 : Nat × Nat × List Nat := (131976, 48, [750912392, 344348296072, 1374603576200, 1375140447112, 1443323052936, 1443859923848, 2955688412040, 3985943692168, 3986480563080, 4329541075848, 4330077946760])
def s34 : Nat × Nat × List Nat := (656264, 34, [214565768, 343811949448, 1374604100488, 2955152065416, 3985944216456, 4329541600136])
def s35 : Nat × Nat × List Nat := (197512, 37, [])
def s36 : Nat × Nat × List Nat := (17288, 50, [])
def s37 : Nat × Nat × List Nat := (82824, 26, [])
def s38 : Nat × Nat × List Nat := (148360, 26, [4330199597960])
def s39 : Nat × Nat × List Nat := (213896, 21, [])
def s40 : Nat × Nat × List Nat := (33672, 54, [1374603477896, 1443322954632, 4329540977544])
def s41 : Nat × Nat × List Nat := (99208, 25, [])
def s42 : Nat × Nat × List Nat := (164744, 27, [214074248, 343811457928, 1374603608968, 1443323085704, 2955151573896, 3985943724936, 4329541108616])
def s43 : Nat × Nat × List Nat := (230280, 22, [])
def s44 : Nat × Nat × List Nat := (836488, 32, [36488072, 42779528, 168608648, 170705800, 571261832, 343598220168, 343633871752, 343640163208, 343734535048, 343765992328, 343768089480, 344168645512, 344617436040, 1855462359944, 1855468651400, 1855594480520, 1855596577672, 1855997133704, 2130304615304, 2130340266888, 2130440930184, 2267779220360, 2267913438088, 2473910387592, 2473935553416, 2473937650568, 2473943942024, 2474036216712, 2474069771144, 2474071868296, 2474438869896, 2474472424328, 2542623572872, 2542629864328, 2542655030152, 2542657127304, 2542663418760, 2542757790600, 2542791345032, 2543158346632, 2543191901064, 3985764041608, 3985772430216, 3985898259336, 3985900356488, 3986300912520, 4054485615496, 4054619833224, 4329329968008, 4329336259464, 4329361425288, 4329363522440, 4329369813896, 4329462088584, 4329464185736, 4329495643016, 4329497740168, 4329864741768, 4329898296200, 4330347086728])
def s45 : Nat × Nat × List Nat := (5000, 37, [])
def s46 : Nat × Nat × List Nat := (9096, 41, [1443322930056, 4329540952968])
def s47 : Nat × Nat × List Nat := (533384, 34, [343811826568, 1443323454344, 3230029849480, 4329541477256])
def s48 : Nat × Nat × List Nat := (140168, 41, [214049672, 343811433352, 1168445154184, 1374603584392, 1443323061128, 2955151549320, 3230029456264, 4054663177096, 4329541084040])
def s49 : Nat × Nat × List Nat := (664456, 34, [214573960, 343811957640, 1168445678472, 1374604108680, 1443323585416, 2955152073608, 3985944224648, 4054663701384, 4329541608328])
def s50 : Nat × Nat × List Nat := (13192, 33, [])
def s51 : Nat × Nat × List Nat := (45960, 27, [])
def s52 : Nat × Nat × List Nat := (2952, 67, [213912456, 343811296136, 1168981887880, 1375140318088, 1443859794824, 2955151412104, 3161309842312, 3230029319048, 3986480434056, 4055199910792, 4261358341000, 4330077817736])
def s53 : Nat × Nat × List Nat := (265096, 25, [])
def s54 : Nat × Nat × List Nat := (527240, 29, [3985944087432, 4054663564168, 4260821994376, 4329541471112])
def s55 : Nat × Nat × List Nat := (68488, 30, [])
def s56 : Nat × Nat × List Nat := (134024, 34, [1374603578248, 1443323054984, 4260821601160, 4329541077896])
def s57 : Nat × Nat × List Nat := (658312, 29, [214567816, 343811951496, 1374604102536, 2955152067464, 3161310497672, 3230029974408, 3985944218504, 4260822125448, 4329541602184])
def s58 : Nat × Nat × List Nat := (199560, 27, [])
def s59 : Nat × Nat × List Nat := (19336, 42, [])
def s60 : Nat × Nat × List Nat := (35720, 47, [1168445049736, 1374603479944, 1443322956680, 3985943595912, 4054663072648, 4260821502856, 4329540979592])
def s61 : Nat × Nat × List Nat := (232328, 22, [])
def s62 : Nat × Nat × List Nat := (838536, 22, [838536, 36490120, 137153416, 168610696, 170707848, 1020054408, 343598222216, 343633873800, 343734537096, 343765994376, 343768091528, 344617438088, 1855426710408, 1855462361992, 1855563025288, 1855594482568, 1855596579720, 2061585140616, 2061620792200, 2061721455496, 2061752912776, 2061755009928, 2130304617352, 2130340268936, 2130440932232, 2130472389512, 2130474486664, 2267745667976, 2267751959432, 2267779222408, 2267879885704, 2267913440136, 2268280441736, 2473910389640, 2473935555464, 2473937652616, 2474069773192, 2474071870344, 2474438871944, 2542623574920, 2542629866376, 2542655032200, 2542657129352, 2542791347080, 2543158348680, 3985738877832, 3985864706952, 3985866804104, 3985898261384, 3985900358536, 3986267360136, 4054452063112, 4054458354568, 4054584183688, 4054586280840, 4054619835272, 4054986836872, 4055469181832, 4260616784776, 4260641950600, 4260742613896, 4260776168328, 4260778265480, 4261145267080, 4261627612040, 4329329970056, 4329336261512, 4329361427336, 4329363524488, 4329462090632, 4329464187784, 4329495645064, 4329497742216, 4329864743816, 4330347088776])
def s63 : Nat × Nat × List Nat := (7048, 30, [])
def s64 : Nat × Nat × List Nat := (11144, 34, [1168445025160, 1443322932104, 4054663048072, 4329540955016])
def s65 : Nat × Nat × List Nat := (535432, 29, [214444936, 343811828616, 1168445549448, 2955151944584, 3161310374792, 3230029851528, 3985944095624, 4054663572360, 4329541479304])
def s66 : Nat × Nat × List Nat := (142216, 34, [214051720, 343811435400, 1168445156232, 1374603586440, 1443323063176, 2955151551368, 3161309981576, 3230029458312, 4329541086088])
def s67 : Nat × Nat × List Nat := (666504, 29, [214576008, 343811959688, 1168445680520, 1374604110728, 1443323587464, 2955152075656, 3161310505864, 3230029982600, 3985944226696, 4054663703432, 4260822133640, 4329541610376])
def s68 : Nat × Nat × List Nat := (15240, 27, [])
def s69 : Nat × Nat × List Nat := (48008, 22, [])
def s70 : Nat × Nat × List Nat := (200, 147, [412529721544, 1375130878152, 3092580925640, 3230028267720, 4192629424328, 4330076766408])
def s71 : Nat × Nat × List Nat := (262344, 87, [67834740936, 4330142040264, 4397539262664])
def s72 : Nat × Nat × List Nat := (524488, 93, [1374594531528, 1512041873608, 4192093077704, 4329540419784])
def s73 : Nat × Nat × List Nat := (65736, 82, [4397523337416, 4397589397704])
def s74 : Nat × Nat × List Nat := (131272, 86, [1237163573448, 1374594138312, 1512041480392, 4192092684488, 4329540026568])
def s75 : Nat × Nat × List Nat := (196808, 68, [])
def s76 : Nat × Nat × List Nat := (721096, 50, [])
def s77 : Nat × Nat × List Nat := (16584, 82, [3111908294856])
def s78 : Nat × Nat × List Nat := (278728, 50, [])
def s79 : Nat × Nat × List Nat := (540872, 51, [])

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
theorem ok75 : shardOK 10 s75.1 s75.2.1 s75.2.2 = true := by decide +kernel
theorem ok76 : shardOK 10 s76.1 s76.2.1 s76.2.2 = true := by decide +kernel
theorem ok77 : shardOK 10 s77.1 s77.2.1 s77.2.2 = true := by decide +kernel
theorem ok78 : shardOK 10 s78.1 s78.2.1 s78.2.2 = true := by decide +kernel
theorem ok79 : shardOK 10 s79.1 s79.2.1 s79.2.2 = true := by decide +kernel

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, s72, s73, s74, s75, s76, s77, s78, s79]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44, ok45, ok46, ok47, ok48, ok49, ok50, ok51, ok52, ok53, ok54, ok55, ok56, ok57, ok58, ok59, ok60, ok61, ok62, ok63, ok64, ok65, ok66, ok67, ok68, ok69, ok70, ok71, ok72, ok73, ok74, ok75, ok76, ok77, ok78, ok79]

end L6CheckK.F1.Shards.S129
