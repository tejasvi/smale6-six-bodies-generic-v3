import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C40
import L6Check.F34.Data.Common
import L6Check.F34.Data.C40
import L6Check.Certs.C0169c544f532d95d
import L6Check.Certs.C08542f04be58456c
import L6Check.Certs.C086535fbd0fd4887
import L6Check.Certs.C0893c77616ebe3a2
import L6Check.Certs.C08a9099e987c7f12
import L6Check.Certs.C08ba53b8337c3b00
import L6Check.Certs.C0b5e05f094ee6d19
import L6Check.Certs.C0c5bc47c4890b747
import L6Check.Certs.C0e7389b26af459fc
import L6Check.Certs.C191a76b2eea82603
import L6Check.Certs.C1ad9c65c60547bbf
import L6Check.Certs.C1c52bd306c931c90
import L6Check.Certs.C231142bfb2a39c82
import L6Check.Certs.C241fc1f51e91d096
import L6Check.Certs.C24adb7bd8995957e
import L6Check.Certs.C253db7bdd82bdb4c
import L6Check.Certs.C28bc9f50a84d7a94
import L6Check.Certs.C2ec4c7324f688829
import L6Check.Certs.C31a1929c3604b3e1
import L6Check.Certs.C33d5510bf795ab41
import L6Check.Certs.C3c27dfacf78b3c81
import L6Check.Certs.C3fd24f1da5fde363
import L6Check.Certs.C489d128f7d9f0ee4
import L6Check.Certs.C4b667c1bf7f99e57
import L6Check.Certs.C4e7490851eed42b1
import L6Check.Certs.C5196a2dbba6aed97
import L6Check.Certs.C52709fbc0a12e485
import L6Check.Certs.C596191694178d9f3
import L6Check.Certs.C5c0379c8bc921747
import L6Check.Certs.C5d8560c735b01cf0
import L6Check.Certs.C5e9b5975e82dcabf
import L6Check.Certs.C71ce67632abd5fee
import L6Check.Certs.C7460b62279020188
import L6Check.Certs.C752433b6f081fff1
import L6Check.Certs.C81ff47566ee05742
import L6Check.Certs.C82b2325ed2a6f936
import L6Check.Certs.C8381c3efb3b24917
import L6Check.Certs.C83deae17b5f2d053
import L6Check.Certs.C8514a8188ce5a529
import L6Check.Certs.C862ae9f4d1db1fa0
import L6Check.Certs.C8716d1bd33a58fe0
import L6Check.Certs.C873ae5a4b2de6b5d
import L6Check.Certs.C88b28ed153620803
import L6Check.Certs.C89de84ac7fe41ee9
import L6Check.Certs.C8d403b01ab872d2c
import L6Check.Certs.C8faedc240372f0dd
import L6Check.Certs.C9038efda0604d1e1
import L6Check.Certs.C903d5f762506ff38
import L6Check.Certs.C90d3e43479986e74
import L6Check.Certs.C947d3e3ce27b3622
import L6Check.Certs.C94b20216b8e1412a
import L6Check.Certs.C9681748baf7b1b3c
import L6Check.Certs.C9f307e1fce49932b
import L6Check.Certs.Ca137255f8b3b67f4
import L6Check.Certs.Ca803305cad9560c4
import L6Check.Certs.Ca8bacf945bd691ad
import L6Check.Certs.Cace3fd8e2040a362
import L6Check.Certs.Cad3844f0717e1c16
import L6Check.Certs.Cae453e6052a1fea2
import L6Check.Certs.Cb1d7d6c5b746e025
import L6Check.Certs.Cb2fd4874fe2d071d
import L6Check.Certs.Cb3613a2be2c59631
import L6Check.Certs.Cb666d8da5fd1b14d
import L6Check.Certs.Cb6b9b264f0d9580a
import L6Check.Certs.Cb7c456ec07072ed7
import L6Check.Certs.Cbb7b28f8875782d5
import L6Check.Certs.Cbc3c5244b70145a9
import L6Check.Certs.Cbe587669321cea0b
import L6Check.Certs.Cbf0d14917b7382bd
import L6Check.Certs.Cc11c7d57d8674628
import L6Check.Certs.Cc32f959fc5096cda
import L6Check.Certs.Cc52c24d12a779c9f
import L6Check.Certs.Ccb82af326ef88e90
import L6Check.Certs.Ccea2cc192799b6f1
import L6Check.Certs.Cd164b0055ae9c2d0
import L6Check.Certs.Cd347bc7b8d748670
import L6Check.Certs.Cdb521498956e69d2
import L6Check.Certs.Cdfa48912008c4ca8
import L6Check.Certs.Ce22c0d46e77e8aed
import L6Check.Certs.Ce2ff9d9f1e6444bc
import L6Check.Certs.Ce3dae7224bb9ecf5
import L6Check.Certs.Ce4c0b509d57d72c5
import L6Check.Certs.Ce814544f4512771f
import L6Check.Certs.Cea2ae820392e76c6
import L6Check.Certs.Cebaf1f548248cc65
import L6Check.Certs.Cee80752e7e6e0fee
import L6Check.Certs.Cf8fe07bf50e67c04
import L6Check.Certs.Cfb0c420a85ba35ef

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 40, cells 0 ≤ cell < 394 of
`data/cells/c40.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 394` of class 40 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 126, core1 := 224, core2 := 44, opn := 0 }. -/
theorem F34S_c40_k0 : checkChunkS 40 (L6.F2.diagOf 40) L6.F2.Data.cells_c40 single_40 links_40 pass_40 open43
    [("0169c544f532d95d", L6.Certs.C0169c544f532d95d), ("08542f04be58456c", L6.Certs.C08542f04be58456c), ("086535fbd0fd4887", L6.Certs.C086535fbd0fd4887), ("0893c77616ebe3a2", L6.Certs.C0893c77616ebe3a2), ("08a9099e987c7f12", L6.Certs.C08a9099e987c7f12), ("08ba53b8337c3b00", L6.Certs.C08ba53b8337c3b00), ("0b5e05f094ee6d19", L6.Certs.C0b5e05f094ee6d19), ("0c5bc47c4890b747", L6.Certs.C0c5bc47c4890b747), ("0e7389b26af459fc", L6.Certs.C0e7389b26af459fc), ("191a76b2eea82603", L6.Certs.C191a76b2eea82603), ("1ad9c65c60547bbf", L6.Certs.C1ad9c65c60547bbf), ("1c52bd306c931c90", L6.Certs.C1c52bd306c931c90), ("231142bfb2a39c82", L6.Certs.C231142bfb2a39c82), ("241fc1f51e91d096", L6.Certs.C241fc1f51e91d096), ("24adb7bd8995957e", L6.Certs.C24adb7bd8995957e), ("253db7bdd82bdb4c", L6.Certs.C253db7bdd82bdb4c), ("28bc9f50a84d7a94", L6.Certs.C28bc9f50a84d7a94), ("2ec4c7324f688829", L6.Certs.C2ec4c7324f688829), ("31a1929c3604b3e1", L6.Certs.C31a1929c3604b3e1), ("33d5510bf795ab41", L6.Certs.C33d5510bf795ab41), ("3c27dfacf78b3c81", L6.Certs.C3c27dfacf78b3c81), ("3fd24f1da5fde363", L6.Certs.C3fd24f1da5fde363), ("489d128f7d9f0ee4", L6.Certs.C489d128f7d9f0ee4), ("4b667c1bf7f99e57", L6.Certs.C4b667c1bf7f99e57), ("4e7490851eed42b1", L6.Certs.C4e7490851eed42b1), ("5196a2dbba6aed97", L6.Certs.C5196a2dbba6aed97), ("52709fbc0a12e485", L6.Certs.C52709fbc0a12e485), ("596191694178d9f3", L6.Certs.C596191694178d9f3), ("5c0379c8bc921747", L6.Certs.C5c0379c8bc921747), ("5d8560c735b01cf0", L6.Certs.C5d8560c735b01cf0), ("5e9b5975e82dcabf", L6.Certs.C5e9b5975e82dcabf), ("71ce67632abd5fee", L6.Certs.C71ce67632abd5fee), ("7460b62279020188", L6.Certs.C7460b62279020188), ("752433b6f081fff1", L6.Certs.C752433b6f081fff1), ("81ff47566ee05742", L6.Certs.C81ff47566ee05742), ("82b2325ed2a6f936", L6.Certs.C82b2325ed2a6f936), ("8381c3efb3b24917", L6.Certs.C8381c3efb3b24917), ("83deae17b5f2d053", L6.Certs.C83deae17b5f2d053), ("8514a8188ce5a529", L6.Certs.C8514a8188ce5a529), ("862ae9f4d1db1fa0", L6.Certs.C862ae9f4d1db1fa0), ("8716d1bd33a58fe0", L6.Certs.C8716d1bd33a58fe0), ("873ae5a4b2de6b5d", L6.Certs.C873ae5a4b2de6b5d), ("88b28ed153620803", L6.Certs.C88b28ed153620803), ("89de84ac7fe41ee9", L6.Certs.C89de84ac7fe41ee9), ("8d403b01ab872d2c", L6.Certs.C8d403b01ab872d2c), ("8faedc240372f0dd", L6.Certs.C8faedc240372f0dd), ("9038efda0604d1e1", L6.Certs.C9038efda0604d1e1), ("903d5f762506ff38", L6.Certs.C903d5f762506ff38), ("90d3e43479986e74", L6.Certs.C90d3e43479986e74), ("947d3e3ce27b3622", L6.Certs.C947d3e3ce27b3622), ("94b20216b8e1412a", L6.Certs.C94b20216b8e1412a), ("9681748baf7b1b3c", L6.Certs.C9681748baf7b1b3c), ("9f307e1fce49932b", L6.Certs.C9f307e1fce49932b), ("a137255f8b3b67f4", L6.Certs.Ca137255f8b3b67f4), ("a803305cad9560c4", L6.Certs.Ca803305cad9560c4), ("a8bacf945bd691ad", L6.Certs.Ca8bacf945bd691ad), ("ace3fd8e2040a362", L6.Certs.Cace3fd8e2040a362), ("ad3844f0717e1c16", L6.Certs.Cad3844f0717e1c16), ("ae453e6052a1fea2", L6.Certs.Cae453e6052a1fea2), ("b1d7d6c5b746e025", L6.Certs.Cb1d7d6c5b746e025), ("b2fd4874fe2d071d", L6.Certs.Cb2fd4874fe2d071d), ("b3613a2be2c59631", L6.Certs.Cb3613a2be2c59631), ("b666d8da5fd1b14d", L6.Certs.Cb666d8da5fd1b14d), ("b6b9b264f0d9580a", L6.Certs.Cb6b9b264f0d9580a), ("b7c456ec07072ed7", L6.Certs.Cb7c456ec07072ed7), ("bb7b28f8875782d5", L6.Certs.Cbb7b28f8875782d5), ("bc3c5244b70145a9", L6.Certs.Cbc3c5244b70145a9), ("be587669321cea0b", L6.Certs.Cbe587669321cea0b), ("bf0d14917b7382bd", L6.Certs.Cbf0d14917b7382bd), ("c11c7d57d8674628", L6.Certs.Cc11c7d57d8674628), ("c32f959fc5096cda", L6.Certs.Cc32f959fc5096cda), ("c52c24d12a779c9f", L6.Certs.Cc52c24d12a779c9f), ("cb82af326ef88e90", L6.Certs.Ccb82af326ef88e90), ("cea2cc192799b6f1", L6.Certs.Ccea2cc192799b6f1), ("d164b0055ae9c2d0", L6.Certs.Cd164b0055ae9c2d0), ("d347bc7b8d748670", L6.Certs.Cd347bc7b8d748670), ("db521498956e69d2", L6.Certs.Cdb521498956e69d2), ("dfa48912008c4ca8", L6.Certs.Cdfa48912008c4ca8), ("e22c0d46e77e8aed", L6.Certs.Ce22c0d46e77e8aed), ("e2ff9d9f1e6444bc", L6.Certs.Ce2ff9d9f1e6444bc), ("e3dae7224bb9ecf5", L6.Certs.Ce3dae7224bb9ecf5), ("e4c0b509d57d72c5", L6.Certs.Ce4c0b509d57d72c5), ("e814544f4512771f", L6.Certs.Ce814544f4512771f), ("ea2ae820392e76c6", L6.Certs.Cea2ae820392e76c6), ("ebaf1f548248cc65", L6.Certs.Cebaf1f548248cc65), ("ee80752e7e6e0fee", L6.Certs.Cee80752e7e6e0fee), ("f8fe07bf50e67c04", L6.Certs.Cf8fe07bf50e67c04), ("fb0c420a85ba35ef", L6.Certs.Cfb0c420a85ba35ef)]
    0 394 { single := 126, core1 := 224, core2 := 44, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
