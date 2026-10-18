import L6K.F1.Shard

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Shards 18220–18314 of the search of Proposition 3.1 (prefixes of `edgesUpTo 6 10`). -/

namespace L6CheckK.F1.Shards.S256

open L6F1 L6K.F1

def s0 : Nat × Nat × List Nat := (16931, 25, [])
def s1 : Nat × Nat × List Nat := (33315, 29, [4329342796323])
def s2 : Nat × Nat × List Nat := (557603, 29, [2680075878947, 3229831692835, 3779587506723, 4329343320611])
def s3 : Nat × Nat × List Nat := (164387, 29, [2954953392675, 3229831299619, 4054465020451, 4329342927395])
def s4 : Nat × Nat × List Nat := (688675, 29, [16417315, 1374405952035, 1649283858979, 2680076010019, 2954953916963, 3504709730851, 3779587637795, 4054465544739, 4329343451683])
def s5 : Nat × Nat × List Nat := (4643, 42, [])
def s6 : Nat × Nat × List Nat := (8739, 47, [4329342771747])
def s7 : Nat × Nat × List Nat := (795171, 27, [])
def s8 : Nat × Nat × List Nat := (205347, 27, [])
def s9 : Nat × Nat × List Nat := (61987, 22, [167834147, 176222755, 1580690633251, 1580715799075, 1580724187683, 1855467876899, 1855593706019, 1855602094627, 2130303840803, 2130345783843, 2130446447139, 2474035442211, 2474068996643, 2474077385251, 2748812685859, 2748946903587, 2748955292195, 3504869536291, 3779713888803, 3779747443235, 4054491132451, 4054625350179, 4329329193507, 4329335484963, 4329360650787, 4329369039395, 4329461314083, 4329469702691, 4329494868515, 4329503257123, 4329863967267, 4330148131363])
def s10 : Nat × Nat × List Nat := (2595, 67, [15731235, 824649452067, 1374942136867, 1649820043811, 1924697950755, 2680075323939, 2954953230883, 3229831137827, 3505245915683, 3780123822627, 4055001729571, 4329879636515])
def s11 : Nat × Nat × List Nat := (264739, 30, [])
def s12 : Nat × Nat × List Nat := (526883, 34, [1649283697187, 1924161604131, 4054465382947, 4329343289891])
def s13 : Nat × Nat × List Nat := (789027, 27, [])
def s14 : Nat × Nat × List Nat := (68131, 30, [])
def s15 : Nat × Nat × List Nat := (133667, 34, [1374405397027, 1924161210915, 3779587082787, 4329342896675])
def s16 : Nat × Nat × List Nat := (657955, 34, [16386595, 824650107427, 1374405921315, 1649283828259, 1924161735203, 2680075979299, 2954953886243, 3229831793187, 4329343420963])
def s17 : Nat × Nat × List Nat := (199203, 27, [])
def s18 : Nat × Nat × List Nat := (18979, 25, [])
def s19 : Nat × Nat × List Nat := (35363, 29, [3504709077539, 3779586984483, 4054464891427, 4329342798371])
def s20 : Nat × Nat × List Nat := (559651, 29, [16288291, 824650009123, 1649283729955, 2680075880995, 2954953787939, 3229831694883, 3504709601827, 4054465415715, 4329343322659])
def s21 : Nat × Nat × List Nat := (166435, 29, [15895075, 824649615907, 1374405429795, 2680075487779, 2954953394723, 3229831301667, 3504709208611, 3779587115555, 4329342929443])
def s22 : Nat × Nat × List Nat := (690723, 29, [16419363, 824650140195, 1374405954083, 1649283861027, 1924161767971, 2680076012067, 2954953919011, 3229831825955, 3504709732899, 3779587639843, 4054465546787, 4329343453731])
def s23 : Nat × Nat × List Nat := (6691, 42, [])
def s24 : Nat × Nat × List Nat := (10787, 47, [1374405274147, 1649283181091, 1924161088035, 3504709052963, 3779586959907, 4054464866851, 4329342773795])
def s25 : Nat × Nat × List Nat := (797219, 22, [])
def s26 : Nat × Nat × List Nat := (207395, 22, [])
def s27 : Nat × Nat × List Nat := (64035, 22, [64035, 42007075, 142670371, 167836195, 176224803, 821099043, 824633784867, 824675727907, 824776391203, 824801557027, 824809945635, 825454819875, 1580548028963, 1580589972003, 1580690635299, 1580715801123, 1580724189731, 1855425935907, 1855467878947, 1855568542243, 1855593708067, 1855602096675, 2130303842851, 2130345785891, 2130446449187, 2130471615011, 2130480003619, 2473903323683, 2473934780963, 2473943169571, 2474068998691, 2474077387299, 2474438097443, 2748781230627, 2748913351203, 2748921739811, 2748946905635, 2748955294243, 2749316004387, 3023659137571, 3023690594851, 3023791258147, 3023824812579, 3023833201187, 3024193911331, 3504695474723, 3504701766179, 3504735320611, 3504835983907, 3504869538339, 3505230248483, 3779573381667, 3779579673123, 3779604838947, 3779613227555, 3779747445283, 3780108155427, 3780392319523, 4054451288611, 4054457580067, 4054583409187, 4054591797795, 4054625352227, 4054986062371, 4055270226467, 4329329195555, 4329335487011, 4329360652835, 4329369041443, 4329461316131, 4329469704739, 4329494870563, 4329503259171, 4329863969315, 4330148133411])
def s28 : Nat × Nat × List Nat := (99, 87, [67966599267, 4330069426275, 4397929070691])
def s29 : Nat × Nat × List Nat := (262243, 50, [])
def s30 : Nat × Nat × List Nat := (524387, 50, [4329533079651, 4397292060771, 4397294157923, 4397795377251])
def s31 : Nat × Nat × List Nat := (786531, 39, [4397124550755, 4397527203939])
def s32 : Nat × Nat × List Nat := (65635, 50, [67698229347, 4397711032419, 4397715226723, 4397912359011])
def s33 : Nat × Nat × List Nat := (327779, 26, [67698491491])
def s34 : Nat × Nat × List Nat := (589923, 24, [4396989087843, 4397023690851, 4397025788003, 4397174685795, 4397178880099, 4397778665571])
def s35 : Nat × Nat × List Nat := (852067, 20, [])
def s36 : Nat × Nat × List Nat := (131171, 50, [])
def s37 : Nat × Nat × List Nat := (393315, 26, [])
def s38 : Nat × Nat × List Nat := (655459, 26, [4329533210723])
def s39 : Nat × Nat × List Nat := (917603, 21, [])
def s40 : Nat × Nat × List Nat := (196707, 39, [4397123960931, 4397375619171])
def s41 : Nat × Nat × List Nat := (458851, 21, [])
def s42 : Nat × Nat × List Nat := (720995, 20, [])
def s43 : Nat × Nat × List Nat := (16483, 43, [])
def s44 : Nat × Nat × List Nat := (802915, 25, [4329462055011, 4329495609443, 4329864708195, 4397124567139, 4397527220323])
def s45 : Nat × Nat × List Nat := (32867, 42, [])
def s46 : Nat × Nat × List Nat := (163939, 42, [])
def s47 : Nat × Nat × List Nat := (4195, 42, [])
def s48 : Nat × Nat × List Nat := (266339, 42, [])
def s49 : Nat × Nat × List Nat := (8291, 43, [])
def s50 : Nat × Nat × List Nat := (204899, 25, [67662717027, 67729825891, 67914375267, 4397123969123, 4397375627363])
def s51 : Nat × Nat × List Nat := (61539, 28, [4397123825763])
def s52 : Nat × Nat × List Nat := (163, 93, [824649449635, 1924697948323, 3229831135395, 4329879634083])
def s53 : Nat × Nat × List Nat := (262307, 51, [])
def s54 : Nat × Nat × List Nat := (524451, 54, [1374405787811, 1924161601699, 4329343287459])
def s55 : Nat × Nat × List Nat := (786595, 41, [])
def s56 : Nat × Nat × List Nat := (65699, 51, [])
def s57 : Nat × Nat × List Nat := (327843, 25, [])
def s58 : Nat × Nat × List Nat := (589987, 25, [])
def s59 : Nat × Nat × List Nat := (852131, 20, [])
def s60 : Nat × Nat × List Nat := (131235, 54, [1649283301539, 1924161208483, 4329342894243])
def s61 : Nat × Nat × List Nat := (393379, 25, [])
def s62 : Nat × Nat × List Nat := (655523, 27, [16384163, 1374405918883, 1649283825827, 1924161732771, 2680075976867, 2954953883811, 4329343418531])
def s63 : Nat × Nat × List Nat := (917667, 22, [])
def s64 : Nat × Nat × List Nat := (196771, 41, [])
def s65 : Nat × Nat × List Nat := (458915, 20, [])
def s66 : Nat × Nat × List Nat := (721059, 22, [])
def s67 : Nat × Nat × List Nat := (16547, 43, [])
def s68 : Nat × Nat × List Nat := (32931, 47, [4329342795939])
def s69 : Nat × Nat × List Nat := (819363, 27, [])
def s70 : Nat × Nat × List Nat := (164003, 47, [824649613475, 1649283334307, 1924161241251, 2954953392291, 3229831299235, 4054465020067, 4329342927011])
def s71 : Nat × Nat × List Nat := (950435, 22, [])
def s72 : Nat × Nat × List Nat := (4259, 43, [])
def s73 : Nat × Nat × List Nat := (8355, 47, [4329342771363])
def s74 : Nat × Nat × List Nat := (532643, 47, [824649982115, 1374405796003, 1924161609891, 2680075853987, 3229831667875, 3779587481763, 4329343295651])
def s75 : Nat × Nat × List Nat := (204963, 27, [])
def s76 : Nat × Nat × List Nat := (729251, 22, [])
def s77 : Nat × Nat × List Nat := (61603, 30, [167833763, 824633782435, 824675725475, 824770097315, 825454817443, 1580684341411, 1580715798691, 1855467876515, 1855593705635, 2130303840419, 2130345783459, 2130440155299, 2474035441827, 2474037538979, 2474068996259, 2748812685475, 2748821074083, 2748946903203, 3023690592419, 3023698981027, 3023791255715, 3023793352867, 3023824810147, 3024193908899, 3779707596963, 4054491132067, 4329329193123, 4329335484579, 4329360650403, 4329369039011, 4329461313699, 4329463410851, 4329494868131, 4329863966883, 4330148130979])
def s78 : Nat × Nat × List Nat := (3235, 50, [])
def s79 : Nat × Nat × List Nat := (265379, 25, [67647048867, 67650194595, 67918630051, 4397510954147, 4397514099875])
def s80 : Nat × Nat × List Nat := (527523, 27, [])
def s81 : Nat × Nat × List Nat := (68771, 25, [67646852259, 67649997987, 67915287715, 4397510757539, 4397513903267])
def s82 : Nat × Nat × List Nat := (134307, 27, [])
def s83 : Nat × Nat × List Nat := (986275, 16, [16714915, 553585827, 4329343749283, 4329880620195])
def s84 : Nat × Nat × List Nat := (19619, 25, [67662531747, 67712863395, 67981298851, 4397526437027, 4397576768675])
def s85 : Nat × Nat × List Nat := (36003, 27, [])
def s86 : Nat × Nat × List Nat := (167075, 22, [])
def s87 : Nat × Nat × List Nat := (7331, 25, [67662519459, 67712851107, 67930954915, 4397526424739, 4397576756387])
def s88 : Nat × Nat × List Nat := (11427, 27, [])
def s89 : Nat × Nat × List Nat := (535715, 22, [])
def s90 : Nat × Nat × List Nat := (64675, 16, [251722915, 788593827, 4329578757283, 4330115628195])
def s91 : Nat × Nat × List Nat := (995, 52, [41944035, 1030792152035, 1030834095075, 1082600195043, 1374928503779, 1374934795235, 1375060624355, 1375143461859, 1855996298211, 2473903260643, 2473934717923, 2473943106531, 2474035381219, 2954979443683, 3229817504739, 3229823796195, 3229848962019, 3229857350627, 3229949625315, 3230032462819, 3299105309667, 3299113698275, 3573951759331, 3573983216611, 3573991605219, 3574083879907, 4055027942371, 4329863906275, 4329866003427, 4329872294883, 4329897460707, 4329905849315, 4329998124003, 4330080961507])
def s92 : Nat × Nat × List Nat := (263139, 28, [4397526680547])
def s93 : Nat × Nat × List Nat := (525283, 30, [570950627, 1031363101667, 1031463764963, 1374390060003, 1374432003043, 1374607115235, 1375061148643, 1855468340195, 1855996822499, 2130304304099, 2130346247139, 2130975392739, 2474438558691, 2474472113123, 2474572776419, 3230487020515, 3298568963043, 3298577351651, 3299105833955, 3573415412707, 3573446869987, 3573455258595, 3573950186467, 3573983740899, 3574084404195, 4054491595747, 4329329656803, 4329335948259, 4329361114083, 4329369502691, 4329461777379, 4329544614883, 4329864430563, 4329897984995, 4329998648291])
def s94 : Nat × Nat × List Nat := (66531, 31, [4397510755299, 4397513901027, 4397576815587])

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
theorem ok80 : shardOK 10 s80.1 s80.2.1 s80.2.2 = true := by decide +kernel
theorem ok81 : shardOK 10 s81.1 s81.2.1 s81.2.2 = true := by decide +kernel
theorem ok82 : shardOK 10 s82.1 s82.2.1 s82.2.2 = true := by decide +kernel
theorem ok83 : shardOK 10 s83.1 s83.2.1 s83.2.2 = true := by decide +kernel
theorem ok84 : shardOK 10 s84.1 s84.2.1 s84.2.2 = true := by decide +kernel
theorem ok85 : shardOK 10 s85.1 s85.2.1 s85.2.2 = true := by decide +kernel
theorem ok86 : shardOK 10 s86.1 s86.2.1 s86.2.2 = true := by decide +kernel
theorem ok87 : shardOK 10 s87.1 s87.2.1 s87.2.2 = true := by decide +kernel
theorem ok88 : shardOK 10 s88.1 s88.2.1 s88.2.2 = true := by decide +kernel
theorem ok89 : shardOK 10 s89.1 s89.2.1 s89.2.2 = true := by decide +kernel
theorem ok90 : shardOK 10 s90.1 s90.2.1 s90.2.2 = true := by decide +kernel
theorem ok91 : shardOK 10 s91.1 s91.2.1 s91.2.2 = true := by decide +kernel
theorem ok92 : shardOK 10 s92.1 s92.2.1 s92.2.2 = true := by decide +kernel
theorem ok93 : shardOK 10 s93.1 s93.2.1 s93.2.2 = true := by decide +kernel
theorem ok94 : shardOK 10 s94.1 s94.2.1 s94.2.2 = true := by decide +kernel

/-- The shards of this module. -/
def shards : List (Nat × Nat × List Nat) := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, s72, s73, s74, s75, s76, s77, s78, s79, s80, s81, s82, s83, s84, s85, s86, s87, s88, s89, s90, s91, s92, s93, s94]

theorem all_ok : shards.all (fun x => shardOK 10 x.1 x.2.1 x.2.2) = true := by
  simp only [shards, List.all_cons, List.all_nil, Bool.and_true, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44, ok45, ok46, ok47, ok48, ok49, ok50, ok51, ok52, ok53, ok54, ok55, ok56, ok57, ok58, ok59, ok60, ok61, ok62, ok63, ok64, ok65, ok66, ok67, ok68, ok69, ok70, ok71, ok72, ok73, ok74, ok75, ok76, ok77, ok78, ok79, ok80, ok81, ok82, ok83, ok84, ok85, ok86, ok87, ok88, ok89, ok90, ok91, ok92, ok93, ok94]

end L6CheckK.F1.Shards.S256
