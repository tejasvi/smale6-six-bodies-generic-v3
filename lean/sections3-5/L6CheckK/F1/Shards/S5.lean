import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 190–220 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S5

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (263168, 192, [2297809863680, 2366535631872, 2435257205760])
def s1 : Nat × Nat × List Nat := (525312, 177, [4187895628800])
def s2 : Nat × Nat × List Nat := (787456, 147, [6377178112, 7454065664, 65431929856, 66506720256, 67583607808, 68658398208])
def s3 : Nat × Nat × List Nat := (66560, 192, [2297809667072, 2366535435264, 2435257009152])
def s4 : Nat × Nat × List Nat := (328704, 192, [2267745158144, 2280630060032, 2289219994624, 2293514961920, 2297809929216, 2336470926336, 2349355828224, 2357945762816, 2362240730112, 2366535697408, 2405192500224, 2418077402112, 2426667336704, 2430962304000, 2435257271296])
def s5 : Nat × Nat × List Nat := (132096, 177, [4187995898880])
def s6 : Nat × Nat × List Nat := (197632, 147, [10520560640, 11597448192, 65280345088, 66355135488, 67432023040, 68506813440])
def s7 : Nat × Nat × List Nat := (17408, 216, [2299957101568])
def s8 : Nat × Nat × List Nat := (279552, 116, [2274187559936, 2299957363712])
def s9 : Nat × Nat × List Nat := (541696, 104, [68318413824])
def s10 : Nat × Nat × List Nat := (803840, 93, [7449887744, 8524678144, 67579429888, 68654220288])
def s11 : Nat × Nat × List Nat := (82944, 116, [2278482330624, 2299957167104])
def s12 : Nat × Nat × List Nat := (345088, 92, [2287072527360, 2291367494656, 2295662461952, 2299957429248])
def s13 : Nat × Nat × List Nat := (148480, 104, [68217357312])
def s14 : Nat × Nat × List Nat := (214016, 93, [11593270272, 12668060672, 67427845120, 68502635520])
def s15 : Nat × Nat × List Nat := (33792, 216, [629179392, 5982159872, 10226795520, 13430195200, 13514081280, 206781318144, 219582333952, 219666220032, 1168325510144, 1181126525952, 1181210412032, 1237034501120, 1237579760640, 1242387481600, 1242932741120, 1246632117248, 1247177376768, 1249835516928, 1249919403008, 1250380776448, 1250464662528, 1272469029888, 1275689206784, 1276763997184, 1279984174080, 1281058964480, 1284212032512, 1284262364160, 1284279141376, 1285270045696, 1285286822912, 1285337154560, 1285353931776, 2281175024640, 2349892404224, 2418613978112, 3311965078528, 3380686652416, 3448867161088, 3449395643392, 3449404032000, 3517580346368, 3517588734976, 3518117217280, 3518125605888])
def s16 : Nat × Nat × List Nat := (295936, 100, [])
def s17 : Nat × Nat × List Nat := (558080, 100, [])
def s18 : Nat × Nat × List Nat := (820224, 87, [67794404352, 4329648718848, 4397014483968])
def s19 : Nat × Nat × List Nat := (99328, 100, [])
def s20 : Nat × Nat × List Nat := (361472, 76, [545620992, 13430522880, 206697759744, 219582661632, 2268290450432, 2281175352320, 2337007830016, 2349892731904, 2405729403904, 2418614305792])
def s21 : Nat × Nat × List Nat := (164864, 100, [])
def s22 : Nat × Nat × List Nat := (230400, 87, [67693151232, 4329799123968, 4397114557440])
def s23 : Nat × Nat × List Nat := (50176, 168, [901825536, 6254806016, 10499441664, 13702841344, 13719618560, 13769950208, 13786727424, 55663707136, 58883884032, 59958674432, 63178851328, 64253641728, 67406709760, 67457041408, 67473818624, 68464722944, 68481500160, 68531831808, 68548609024, 3518398252032])
def s24 : Nat × Nat × List Nat := (312320, 86, [6187959296, 13703103488, 14777893888, 67390194688, 68464985088])
def s25 : Nat × Nat × List Nat := (574464, 82, [4397014238208, 4397278479360])
def s26 : Nat × Nat × List Nat := (115712, 86, [10482729984, 13702906880, 14777697280, 67389998080, 68464788480])
def s27 : Nat × Nat × List Nat := (377856, 67, [818267136, 6188024832, 10482992128, 13703169024, 14777959424, 55580148736, 58800325632, 59875116032, 63095292928, 64170083328, 67390260224, 68465050624])
def s28 : Nat × Nat × List Nat := (181248, 82, [4397114508288, 4397378749440])
def s29 : Nat × Nat × List Nat := (5120, 216, [2367609115648])
def s30 : Nat × Nat × List Nat := (267264, 116, [2341839574016, 2367609377792])

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

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30]

end L6CheckK.F1.Shards.S5
