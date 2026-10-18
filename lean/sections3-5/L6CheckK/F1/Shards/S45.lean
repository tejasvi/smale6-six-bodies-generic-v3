import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 2580–2624 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S45

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (393232, 104, [68217602064])
def s1 : Nat × Nat × List Nat := (655376, 100, [])
def s2 : Nat × Nat × List Nat := (917520, 82, [4397052330000, 4397253656592])
def s3 : Nat × Nat × List Nat := (196624, 147, [4078108688, 11660361744, 58837893136, 59912683536, 67494936592, 68569726992])
def s4 : Nat × Nat × List Nat := (458768, 93, [11593515024, 12668305424, 67428089872, 68502880272])
def s5 : Nat × Nat × List Nat := (720912, 87, [67882385424, 4329610870800, 4397052133392])
def s6 : Nat × Nat × List Nat := (16400, 192, [2291367165968, 2772535623696, 2841257197584])
def s7 : Nat × Nat × List Nat := (278544, 116, [2280630009872, 2299957362704])
def s8 : Nat × Nat × List Nat := (540688, 100, [])
def s9 : Nat × Nat × List Nat := (802832, 86, [6377193488, 7449886736, 8524677136, 67579428880, 68654219280])
def s10 : Nat × Nat × List Nat := (81936, 192, [2267744911376, 2274187362320, 2287072264208, 2289219747856, 2291367231504, 2748913369104, 2755355820048, 2768240721936, 2770388205584, 2772535689232, 2817634942992, 2824077393936, 2836962295824, 2839109779472, 2841257263120])
def s11 : Nat × Nat × List Nat := (344080, 92, [2293514977296, 2295662460944, 2297809944592, 2299957428240])
def s12 : Nat × Nat × List Nat := (606224, 76, [671694864, 7114145808, 619014864912, 625457315856, 2268416524304, 2274858975248, 2749450764304, 2755893215248, 2818172338192, 2824614789136])
def s13 : Nat × Nat × List Nat := (868368, 67, [1007501328, 4229775376, 6377259024, 7449952272, 8524742672, 62211833872, 63284527120, 64359317520, 65432010768, 66506801168, 67579494416, 68654284816])
def s14 : Nat × Nat × List Nat := (32784, 177, [3769135824912])
def s15 : Nat × Nat × List Nat := (294928, 104, [68192337936])
def s16 : Nat × Nat × List Nat := (557072, 100, [])
def s17 : Nat × Nat × List Nat := (819216, 82, [4397077397520, 4397278724112])
def s18 : Nat × Nat × List Nat := (49168, 147, [6187696144, 13769949200, 58799996944, 59874787344, 67457040400, 68531830800])
def s19 : Nat × Nat × List Nat := (311312, 93, [13703102480, 14777892880, 67390193680, 68464984080])
def s20 : Nat × Nat × List Nat := (573456, 87, [67857072144, 4329648472080, 4397077151760])
def s21 : Nat × Nat × List Nat := (4112, 216, [2773609353232])
def s22 : Nat × Nat × List Nat := (266256, 106, [])
def s23 : Nat × Nat × List Nat := (528400, 98, [3984725643280])
def s24 : Nat × Nat × List Nat := (790544, 82, [4245426192, 4249620496, 6380326928, 6397104144, 8527810576, 8540393488, 8544587792, 62231678992, 64379162640, 66526646288, 68653158416, 68657352720, 68669935632, 68674129936])
def s25 : Nat × Nat × List Nat := (69648, 116, [2752134582288, 2773609418768])
def s26 : Nat × Nat × List Nat := (331792, 58, [])
def s27 : Nat × Nat × List Nat := (593936, 48, [3892908048, 2752671977488])
def s28 : Nat × Nat × List Nat := (856080, 43, [4228714512, 68653223952])
def s29 : Nat × Nat × List Nat := (135184, 104, [68283404304])
def s30 : Nat × Nat × List Nat := (397328, 49, [])
def s31 : Nat × Nat × List Nat := (659472, 46, [4397051023376])
def s32 : Nat × Nat × List Nat := (921616, 40, [67831205904, 4396985225232, 4396988370960, 4397052334096])
def s33 : Nat × Nat × List Nat := (200720, 93, [4077064208, 12734107664, 59911639056, 68568682512])
def s34 : Nat × Nat × List Nat := (462864, 47, [68501835792])
def s35 : Nat × Nat × List Nat := (725008, 43, [])
def s36 : Nat × Nat × List Nat := (20496, 116, [2754282016784, 2773609369616])
def s37 : Nat × Nat × List Nat := (282640, 58, [])
def s38 : Nat × Nat × List Nat := (544784, 48, [6040342544, 2754819411984])
def s39 : Nat × Nat × List Nat := (806928, 43, [6376149008, 68653174800])
def s40 : Nat × Nat × List Nat := (86032, 92, [2767166984208, 2769314467856, 2771461951504, 2773609435152])
def s41 : Nat × Nat × List Nat := (348176, 42, [])
def s42 : Nat × Nat × List Nat := (610320, 31, [])
def s43 : Nat × Nat × List Nat := (872464, 29, [62210789392, 64358273040, 66505756688, 68653240336])
def s44 : Nat × Nat × List Nat := (36880, 104, [68258140176])

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

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44]

end L6CheckK.F1.Shards.S45
