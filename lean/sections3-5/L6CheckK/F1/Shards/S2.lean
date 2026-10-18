import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 45–83 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S2

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (49152, 297, [817938432, 55579820032, 58816774144, 59891564544, 63162073088, 64236863488, 67473817600, 68548608000, 3505513349120, 3711703236608, 3780424810496, 3986681806848, 4055403380736, 4261593268224, 4330314842112])
def s1 : Nat × Nat × List Nat := (311296, 147, [10482925568, 13719879680, 63095226368, 64170016768, 67406970880, 68481761280])
def s2 : Nat × Nat × List Nat := (573440, 147, [619295850496, 825485737984, 3986548113408, 4055269687296, 4261459574784, 4330181148672])
def s3 : Nat × Nat × List Nat := (114688, 147, [6187761664, 13770014720, 58800062464, 59874852864, 67457105920, 68531896320])
def s4 : Nat × Nat × List Nat := (376832, 67, [67390259200, 68465049600])
def s5 : Nat × Nat × List Nat := (638976, 63, [67857137664, 4329384296448, 4397077217280])
def s6 : Nat × Nat × List Nat := (180224, 147, [344417550336, 825586008064, 3711669813248, 3780391387136, 4261559844864, 4330281418752])
def s7 : Nat × Nat × List Nat := (442368, 63, [67705946112, 4329535094784, 4397127352320])
def s8 : Nat × Nat × List Nat := (704512, 67, [4261426151424, 4330147725312])
def s9 : Nat × Nat × List Nat := (4096, 378, [2354724212736, 2492188332032, 2629635674112, 2767166902272, 2904614244352, 3042078363648, 3179525705728])
def s10 : Nat × Nat × List Nat := (266240, 192, [2363314409472, 2500778528768, 2638225870848])
def s11 : Nat × Nat × List Nat := (528384, 177, [3978283192320])
def s12 : Nat × Nat × List Nat := (790528, 147, [4232843264, 6392909824, 62210707456, 64362385408, 66522451968, 68674129920])
def s13 : Nat × Nat × List Nat := (69632, 192, [2359019245568, 2771461935104, 2908909277184])
def s14 : Nat × Nat × List Nat := (331776, 92, [2367609442304])
def s15 : Nat × Nat × List Nat := (593920, 76, [])
def s16 : Nat × Nat × List Nat := (856064, 67, [66505740288, 68657418240])
def s17 : Nat × Nat × List Nat := (135168, 177, [3699059593216])
def s18 : Nat × Nat × List Nat := (397312, 76, [])
def s19 : Nat × Nat × List Nat := (659456, 76, [])
def s20 : Nat × Nat × List Nat := (921600, 63, [67835400192, 4329406599168, 4397005148160])
def s21 : Nat × Nat × List Nat := (200704, 147, [4081258496, 10586624000, 57764155392, 59915833344, 66421198848, 68572876800])
def s22 : Nat × Nat × List Nat := (462848, 67, [66354352128, 68506030080])
def s23 : Nat × Nat × List Nat := (724992, 63, [67885535232, 4329356070912, 4397055283200])
def s24 : Nat × Nat × List Nat := (20480, 192, [2494335832064, 2769314402304, 3044225863680])
def s25 : Nat × Nat × List Nat := (282624, 92, [2502926028800])
def s26 : Nat × Nat × List Nat := (544768, 76, [])
def s27 : Nat × Nat × List Nat := (806912, 67, [64358207488, 68669952000])
def s28 : Nat × Nat × List Nat := (86016, 92, [2773609435136])
def s29 : Nat × Nat × List Nat := (348160, 42, [])
def s30 : Nat × Nat × List Nat := (610304, 31, [])
def s31 : Nat × Nat × List Nat := (872448, 29, [68653240320])
def s32 : Nat × Nat × List Nat := (151552, 76, [])
def s33 : Nat × Nat × List Nat := (413696, 31, [])
def s34 : Nat × Nat × List Nat := (675840, 28, [])
def s35 : Nat × Nat × List Nat := (937984, 25, [])
def s36 : Nat × Nat × List Nat := (217088, 67, [59911655424, 68568698880])
def s37 : Nat × Nat × List Nat := (479232, 29, [68501852160])
def s38 : Nat × Nat × List Nat := (741376, 25, [])

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

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38]

end L6CheckK.F1.Shards.S2
