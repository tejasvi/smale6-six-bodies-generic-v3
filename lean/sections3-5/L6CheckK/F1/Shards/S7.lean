import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 280–316 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S7

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (275456, 86, [7255372800, 13693629440, 15845307392, 66306978816, 68458656768])
def s1 : Nat × Nat × List Nat := (537600, 82, [4397020492800, 4397287879680])
def s2 : Nat × Nat × List Nat := (78848, 86, [11550143488, 13693432832, 15845110784, 66306782208, 68458460160])
def s3 : Nat × Nat × List Nat := (340992, 67, [808793088, 7255438336, 11550405632, 13693694976, 15845372928, 55573820416, 57717109760, 59868787712, 62012077056, 64163755008, 66307044352, 68458722304])
def s4 : Nat × Nat × List Nat := (144384, 82, [4397120762880, 4397388149760])
def s5 : Nat × Nat × List Nat := (29696, 82, [7318041600, 7334818816, 11562677248, 11629786112, 15857644544, 15907976192, 15924753408, 55653200896, 59948168192, 64243135488, 68454216704, 68470993920, 68521325568, 68538102784])
def s6 : Nat × Nat × List Nat := (291840, 43, [7251194880, 68454478848])
def s7 : Nat × Nat × List Nat := (553984, 40, [67849712640, 4397019460608, 4397020509184, 4397032043520])
def s8 : Nat × Nat × List Nat := (95232, 43, [11545965568, 68454282240])
def s9 : Nat × Nat × List Nat := (357376, 29, [55569642496, 59864609792, 64159577088, 68454544384])
def s10 : Nat × Nat × List Nat := (160768, 40, [67698324480, 4397119730688, 4397120779264, 4397182645248])
def s11 : Nat × Nat × List Nat := (46080, 82, [3518386713600])
def s12 : Nat × Nat × List Nat := (308224, 39, [67677500416])
def s13 : Nat × Nat × List Nat := (570368, 39, [])
def s14 : Nat × Nat × List Nat := (111616, 39, [67727635456])
def s15 : Nat × Nat × List Nat := (373760, 25, [])
def s16 : Nat × Nat × List Nat := (177152, 39, [])
def s17 : Nat × Nat × List Nat := (2048, 378, [860068251648, 861145139200, 862219929600, 876441765888, 877516556288, 878593443840, 879668234240])
def s18 : Nat × Nat × List Nat := (264192, 177, [4188147025920])
def s19 : Nat × Nat × List Nat := (526336, 192, [1959580403712, 1960657291264, 1961732081664])
def s20 : Nat × Nat × List Nat := (788480, 147, [344606902272, 413332670464, 4124176025600, 4192897599488, 4261623367680, 4330344941568])
def s21 : Nat × Nat × List Nat := (67584, 177, [4188197160960])
def s22 : Nat × Nat × List Nat := (133120, 192, [1959580010496, 1960656898048, 1961731688448])
def s23 : Nat × Nat × List Nat := (657408, 192, [35435186176, 36512073728, 37586864128, 860068907008, 861145794560, 862220584960, 1409824720896, 1410901608448, 1411976398848, 1684702627840, 1685779515392, 1686854305792, 1959580534784, 1960657422336, 1961732212736])
def s24 : Nat × Nat × List Nat := (198656, 147, [619333224448, 688058992640, 4124024440832, 4192746014720, 4261471782912, 4330193356800])
def s25 : Nat × Nat × List Nat := (18432, 216, [440420352, 3658500096, 18426644480, 19495143424, 19767773184, 344006346752, 363061069824, 363333699584, 618783590400, 637838313472, 638110943232, 824906369024, 825074141184, 828124448768, 828292220928, 842892593152, 843060365312, 843961092096, 844128864256, 844233721856, 844401494016, 860340897792, 861413591040, 862488381440, 876445976576, 877520766976, 878325024768, 878589265920, 878593460224, 879395620864, 879399815168, 879664056320, 879668250624, 2287239972864, 2493396305920, 2562117879808, 2768274212864, 2836995786752, 3043017902080, 3043118565376, 3043152119808, 3111705921536, 3111739475968, 3111840139264, 3111873693696])
def s26 : Nat × Nat × List Nat := (280576, 100, [])
def s27 : Nat × Nat × List Nat := (542720, 100, [])
def s28 : Nat × Nat × List Nat := (804864, 87, [68234790912, 4329409628160, 4397001885696])
def s29 : Nat × Nat × List Nat := (83968, 100, [])
def s30 : Nat × Nat × List Nat := (149504, 100, [])
def s31 : Nat × Nat × List Nat := (673792, 76, [273303552, 3491383296, 35707832320, 36780525568, 37855315968, 824907024384, 828125104128, 860341553152, 861414246400, 862489036800])
def s32 : Nat × Nat × List Nat := (215040, 87, [68385196032, 4329358706688, 4397051627520])
def s33 : Nat × Nat × List Nat := (34816, 216, [2097018865664])
def s34 : Nat × Nat × List Nat := (296960, 104, [4329664972800])
def s35 : Nat × Nat × List Nat := (559104, 116, [447751948288, 2097019389952])
def s36 : Nat × Nat × List Nat := (821248, 93, [413324314624, 482045888512, 4261615011840, 4330336585728])

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

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36]

end L6CheckK.F1.Shards.S7
