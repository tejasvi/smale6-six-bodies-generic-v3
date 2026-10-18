import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C01e8d2b5ff000a8a
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C0e328c1c0bdd8f2b
import L6Check.Certs.C0ef486cb83932658
import L6Check.Certs.C1154f63f4ae46ba1
import L6Check.Certs.C1271e1e068049497
import L6Check.Certs.C139ca930471bb3cc
import L6Check.Certs.C153c8a5f192b8602
import L6Check.Certs.C159170cc8fce2871
import L6Check.Certs.C16083f379b58e8b9
import L6Check.Certs.C17d125efbb380559
import L6Check.Certs.C1a140fd715c8977d
import L6Check.Certs.C1e2967b0cae77bfc
import L6Check.Certs.C1e5824ec76e4c67e
import L6Check.Certs.C2690962aefef2d17
import L6Check.Certs.C297fcb0c1a7e9480
import L6Check.Certs.C29a9f1035fca10b0
import L6Check.Certs.C2c73043df08938eb
import L6Check.Certs.C2ca77d6d0029d619
import L6Check.Certs.C359d5646898dc827
import L6Check.Certs.C3aa53c63b1a89ec3
import L6Check.Certs.C42955a12632fff8e
import L6Check.Certs.C42f5f99b3dfc4d2c
import L6Check.Certs.C45b7edf950821bea
import L6Check.Certs.C45c07671fbddc583
import L6Check.Certs.C4627b4cd3ad10f72
import L6Check.Certs.C478085dbb3e0b13e
import L6Check.Certs.C493681a192bc06ca
import L6Check.Certs.C4be41576b19f548d
import L6Check.Certs.C4eedbedb34ed9102
import L6Check.Certs.C510cd38a096e77e7
import L6Check.Certs.C594441ba6f9b8a26
import L6Check.Certs.C5baf97584add4ae3
import L6Check.Certs.C6291005794413fc6
import L6Check.Certs.C679323c60894051f
import L6Check.Certs.C6ab714f4d84692a6
import L6Check.Certs.C6c61163370247b04
import L6Check.Certs.C6eaaae5128d29302
import L6Check.Certs.C72112d56716fc785
import L6Check.Certs.C7da3e6f6ffe488a9
import L6Check.Certs.C840c82e8ce38adf2
import L6Check.Certs.C84968ef0be6b838b
import L6Check.Certs.C897da59625543f7b
import L6Check.Certs.C8f3bf60abd4be41a
import L6Check.Certs.C906ea918de4784ff
import L6Check.Certs.C93239f06053d3f20
import L6Check.Certs.C94c26c9da4b1c68c
import L6Check.Certs.C957be199b7c614c7
import L6Check.Certs.C9602c18df168a1fe
import L6Check.Certs.C98a0aeddbafd484e
import L6Check.Certs.C98bfac106adc21cf
import L6Check.Certs.C9cb7f0a9d38ed402
import L6Check.Certs.C9d68012519eb9ef4
import L6Check.Certs.C9e8384ef47000134
import L6Check.Certs.C9fae95aeb0dc9cee
import L6Check.Certs.Ca05f78c08e847399
import L6Check.Certs.Ca12d97d2fcf138b4
import L6Check.Certs.Ca152f608aaf33d4a
import L6Check.Certs.Ca1c0ae0a10456276
import L6Check.Certs.Ca36399fc6144633e
import L6Check.Certs.Ca420499ed3238b77
import L6Check.Certs.Ca79ff001c9051e4d
import L6Check.Certs.Cad7c41850e85fffa
import L6Check.Certs.Caf70e1b959f45691
import L6Check.Certs.Cb1eb7e6de97fa058
import L6Check.Certs.Cb29576f4f3a1aab7
import L6Check.Certs.Cbece27e87a1bd47a
import L6Check.Certs.Cc141c278d23fd57b
import L6Check.Certs.Cc46d7d6de70322e8
import L6Check.Certs.Cc534bde108120593
import L6Check.Certs.Cd446af27446827db
import L6Check.Certs.Cdabfd0fabd0b3f0c
import L6Check.Certs.Cdd3879243137f416
import L6Check.Certs.Cddc6cf1e376e9505
import L6Check.Certs.Cdeab948fec8868d2
import L6Check.Certs.Cdeed67c57f7c2870
import L6Check.Certs.Cdf52947002efabf9
import L6Check.Certs.Ce4e6dba09ed9495f
import L6Check.Certs.Ce561a9e2067dd9d1
import L6Check.Certs.Cec0adc75822f13a3
import L6Check.Certs.Cecdc3c4e37764455
import L6Check.Certs.Cefa2e2bcd1dc637d
import L6Check.Certs.Cf0f2997f961f3435
import L6Check.Certs.Cf217c2199a2e4cbf
import L6Check.Certs.Cf37e67fc6846088b
import L6Check.Certs.Cf6344910dd62038d
import L6Check.Certs.Cf8c3a2078e9a9120
import L6Check.Certs.Cf98f5c9c1997da63
import L6Check.Certs.Cf9b0e89c8d83f309
import L6Check.Certs.Cfce5422db8977d36
import L6Check.Certs.Cfedfe4ab747e9ba0

/-! F3/F4 (Proposition 5.3), class 3, cells 42000 ≤ cell < 43500 of `data/cells/c3.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `42000 ≤ cell < 43500` of class 3 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 1240, core1 := 216, core2 := 44, opn := 0 }. -/
theorem F34_c3_k28 : checkChunk 3 n6 cells_3 single_3 links_3 pass_3 open43
    [("01e8d2b5ff000a8a", L6.Certs.C01e8d2b5ff000a8a), ("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("0e328c1c0bdd8f2b", L6.Certs.C0e328c1c0bdd8f2b), ("0ef486cb83932658", L6.Certs.C0ef486cb83932658), ("1154f63f4ae46ba1", L6.Certs.C1154f63f4ae46ba1), ("1271e1e068049497", L6.Certs.C1271e1e068049497), ("139ca930471bb3cc", L6.Certs.C139ca930471bb3cc), ("153c8a5f192b8602", L6.Certs.C153c8a5f192b8602), ("159170cc8fce2871", L6.Certs.C159170cc8fce2871), ("16083f379b58e8b9", L6.Certs.C16083f379b58e8b9), ("17d125efbb380559", L6.Certs.C17d125efbb380559), ("1a140fd715c8977d", L6.Certs.C1a140fd715c8977d), ("1e2967b0cae77bfc", L6.Certs.C1e2967b0cae77bfc), ("1e5824ec76e4c67e", L6.Certs.C1e5824ec76e4c67e), ("2690962aefef2d17", L6.Certs.C2690962aefef2d17), ("297fcb0c1a7e9480", L6.Certs.C297fcb0c1a7e9480), ("29a9f1035fca10b0", L6.Certs.C29a9f1035fca10b0), ("2c73043df08938eb", L6.Certs.C2c73043df08938eb), ("2ca77d6d0029d619", L6.Certs.C2ca77d6d0029d619), ("359d5646898dc827", L6.Certs.C359d5646898dc827), ("3aa53c63b1a89ec3", L6.Certs.C3aa53c63b1a89ec3), ("42955a12632fff8e", L6.Certs.C42955a12632fff8e), ("42f5f99b3dfc4d2c", L6.Certs.C42f5f99b3dfc4d2c), ("45b7edf950821bea", L6.Certs.C45b7edf950821bea), ("45c07671fbddc583", L6.Certs.C45c07671fbddc583), ("4627b4cd3ad10f72", L6.Certs.C4627b4cd3ad10f72), ("478085dbb3e0b13e", L6.Certs.C478085dbb3e0b13e), ("493681a192bc06ca", L6.Certs.C493681a192bc06ca), ("4be41576b19f548d", L6.Certs.C4be41576b19f548d), ("4eedbedb34ed9102", L6.Certs.C4eedbedb34ed9102), ("510cd38a096e77e7", L6.Certs.C510cd38a096e77e7), ("594441ba6f9b8a26", L6.Certs.C594441ba6f9b8a26), ("5baf97584add4ae3", L6.Certs.C5baf97584add4ae3), ("6291005794413fc6", L6.Certs.C6291005794413fc6), ("679323c60894051f", L6.Certs.C679323c60894051f), ("6ab714f4d84692a6", L6.Certs.C6ab714f4d84692a6), ("6c61163370247b04", L6.Certs.C6c61163370247b04), ("6eaaae5128d29302", L6.Certs.C6eaaae5128d29302), ("72112d56716fc785", L6.Certs.C72112d56716fc785), ("7da3e6f6ffe488a9", L6.Certs.C7da3e6f6ffe488a9), ("840c82e8ce38adf2", L6.Certs.C840c82e8ce38adf2), ("84968ef0be6b838b", L6.Certs.C84968ef0be6b838b), ("897da59625543f7b", L6.Certs.C897da59625543f7b), ("8f3bf60abd4be41a", L6.Certs.C8f3bf60abd4be41a), ("906ea918de4784ff", L6.Certs.C906ea918de4784ff), ("93239f06053d3f20", L6.Certs.C93239f06053d3f20), ("94c26c9da4b1c68c", L6.Certs.C94c26c9da4b1c68c), ("957be199b7c614c7", L6.Certs.C957be199b7c614c7), ("9602c18df168a1fe", L6.Certs.C9602c18df168a1fe), ("98a0aeddbafd484e", L6.Certs.C98a0aeddbafd484e), ("98bfac106adc21cf", L6.Certs.C98bfac106adc21cf), ("9cb7f0a9d38ed402", L6.Certs.C9cb7f0a9d38ed402), ("9d68012519eb9ef4", L6.Certs.C9d68012519eb9ef4), ("9e8384ef47000134", L6.Certs.C9e8384ef47000134), ("9fae95aeb0dc9cee", L6.Certs.C9fae95aeb0dc9cee), ("a05f78c08e847399", L6.Certs.Ca05f78c08e847399), ("a12d97d2fcf138b4", L6.Certs.Ca12d97d2fcf138b4), ("a152f608aaf33d4a", L6.Certs.Ca152f608aaf33d4a), ("a1c0ae0a10456276", L6.Certs.Ca1c0ae0a10456276), ("a36399fc6144633e", L6.Certs.Ca36399fc6144633e), ("a420499ed3238b77", L6.Certs.Ca420499ed3238b77), ("a79ff001c9051e4d", L6.Certs.Ca79ff001c9051e4d), ("ad7c41850e85fffa", L6.Certs.Cad7c41850e85fffa), ("af70e1b959f45691", L6.Certs.Caf70e1b959f45691), ("b1eb7e6de97fa058", L6.Certs.Cb1eb7e6de97fa058), ("b29576f4f3a1aab7", L6.Certs.Cb29576f4f3a1aab7), ("bece27e87a1bd47a", L6.Certs.Cbece27e87a1bd47a), ("c141c278d23fd57b", L6.Certs.Cc141c278d23fd57b), ("c46d7d6de70322e8", L6.Certs.Cc46d7d6de70322e8), ("c534bde108120593", L6.Certs.Cc534bde108120593), ("d446af27446827db", L6.Certs.Cd446af27446827db), ("dabfd0fabd0b3f0c", L6.Certs.Cdabfd0fabd0b3f0c), ("dd3879243137f416", L6.Certs.Cdd3879243137f416), ("ddc6cf1e376e9505", L6.Certs.Cddc6cf1e376e9505), ("deab948fec8868d2", L6.Certs.Cdeab948fec8868d2), ("deed67c57f7c2870", L6.Certs.Cdeed67c57f7c2870), ("df52947002efabf9", L6.Certs.Cdf52947002efabf9), ("e4e6dba09ed9495f", L6.Certs.Ce4e6dba09ed9495f), ("e561a9e2067dd9d1", L6.Certs.Ce561a9e2067dd9d1), ("ec0adc75822f13a3", L6.Certs.Cec0adc75822f13a3), ("ecdc3c4e37764455", L6.Certs.Cecdc3c4e37764455), ("efa2e2bcd1dc637d", L6.Certs.Cefa2e2bcd1dc637d), ("f0f2997f961f3435", L6.Certs.Cf0f2997f961f3435), ("f217c2199a2e4cbf", L6.Certs.Cf217c2199a2e4cbf), ("f37e67fc6846088b", L6.Certs.Cf37e67fc6846088b), ("f6344910dd62038d", L6.Certs.Cf6344910dd62038d), ("f8c3a2078e9a9120", L6.Certs.Cf8c3a2078e9a9120), ("f98f5c9c1997da63", L6.Certs.Cf98f5c9c1997da63), ("f9b0e89c8d83f309", L6.Certs.Cf9b0e89c8d83f309), ("fce5422db8977d36", L6.Certs.Cfce5422db8977d36), ("fedfe4ab747e9ba0", L6.Certs.Cfedfe4ab747e9ba0)]
    42000 43500 { single := 1240, core1 := 216, core2 := 44, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
