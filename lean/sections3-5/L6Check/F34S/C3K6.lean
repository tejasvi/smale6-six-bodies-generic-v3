import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C3
import L6Check.F34.Data.Common
import L6Check.F34.Data.C3
import L6Check.Certs.C059204b512e177a4
import L6Check.Certs.C05bf22ee20141b09
import L6Check.Certs.C07018856a1764b34
import L6Check.Certs.C07242f678e81f55c
import L6Check.Certs.C1154f63f4ae46ba1
import L6Check.Certs.C177b52d2d54e4b01
import L6Check.Certs.C1a140fd715c8977d
import L6Check.Certs.C1e2967b0cae77bfc
import L6Check.Certs.C1fc5829f7e64f575
import L6Check.Certs.C21aff3926f57567e
import L6Check.Certs.C2609698da6259546
import L6Check.Certs.C27b7c036daadb8d7
import L6Check.Certs.C28bd5f3910159820
import L6Check.Certs.C2fc74d4784f04bdc
import L6Check.Certs.C391c3c7fc731914e
import L6Check.Certs.C3c01e156ee5de7c4
import L6Check.Certs.C3e295c2451418f87
import L6Check.Certs.C44cb11ddbf22c8c7
import L6Check.Certs.C493681a192bc06ca
import L6Check.Certs.C4eedbedb34ed9102
import L6Check.Certs.C5038acf7c79a60be
import L6Check.Certs.C523a70a88966a74f
import L6Check.Certs.C534b536c8c5ed01a
import L6Check.Certs.C541cb148fdb38933
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5d00be4fed6c02b8
import L6Check.Certs.C62478f59f01913b0
import L6Check.Certs.C6377753c94c99900
import L6Check.Certs.C6387869e3a9615e0
import L6Check.Certs.C6451939f227eb79b
import L6Check.Certs.C679323c60894051f
import L6Check.Certs.C69425143f6838587
import L6Check.Certs.C699d11d871de775a
import L6Check.Certs.C6ab714f4d84692a6
import L6Check.Certs.C6c5e96bff34ebc16
import L6Check.Certs.C6cb81b64dfa2ff3a
import L6Check.Certs.C7437b7380293085a
import L6Check.Certs.C75077c3232d28783
import L6Check.Certs.C7f10f1f3767082da
import L6Check.Certs.C840c82e8ce38adf2
import L6Check.Certs.C842183a5e7ad2f00
import L6Check.Certs.C84e3ce8fdc777ad7
import L6Check.Certs.C88c3ca1abda77158
import L6Check.Certs.C897da59625543f7b
import L6Check.Certs.C8b7828b5e04dab19
import L6Check.Certs.C8bbe78015a3100aa
import L6Check.Certs.C8e65bfc835be8eb5
import L6Check.Certs.C90aad8bec4c0fe2e
import L6Check.Certs.C90b15a7e7c4e4eb3
import L6Check.Certs.C91187e8d7dfeee9b
import L6Check.Certs.C913a22eee130223e
import L6Check.Certs.C96961b1def74ebc2
import L6Check.Certs.C98575e8f84629ff1
import L6Check.Certs.C9aca347471741b84
import L6Check.Certs.C9b5bed43783c5f61
import L6Check.Certs.C9ff5f6dec2baab1d
import L6Check.Certs.Ca03049e6b247dba6
import L6Check.Certs.Ca354a82d8fa692c1
import L6Check.Certs.Ca65a37706335f71b
import L6Check.Certs.Ca7a5827ea915ed3e
import L6Check.Certs.Cae2ab36ffe129341
import L6Check.Certs.Cb6efb92403750ecd
import L6Check.Certs.Cbece27e87a1bd47a
import L6Check.Certs.Cc141c278d23fd57b
import L6Check.Certs.Cc455eb28dd8b707c
import L6Check.Certs.Cc4cc46eaa79216c8
import L6Check.Certs.Cc78dafe01015e669
import L6Check.Certs.Cce07296cae588c90
import L6Check.Certs.Cd399a12f11dfae38
import L6Check.Certs.Cd636f830987946d9
import L6Check.Certs.Cdd7f886d75662f5a
import L6Check.Certs.Ce20b0e5d198f78df
import L6Check.Certs.Ce27952f8372676c2
import L6Check.Certs.Ce36e575c21c81dd7
import L6Check.Certs.Ce3e8d223b87fe872
import L6Check.Certs.Ce484fe3d072232cf
import L6Check.Certs.Ce8dd97920792318b
import L6Check.Certs.Cec3b06053a4dea2f
import L6Check.Certs.Cecdc3c4e37764455
import L6Check.Certs.Ced82aeeb929ba915
import L6Check.Certs.Cf21024ebbab7964d
import L6Check.Certs.Cf6344910dd62038d
import L6Check.Certs.Cf9d89ba1685be5ab

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 3, cells 9000 ≤ cell < 10500 of
`data/cells/c3.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `9000 ≤ cell < 10500` of class 3 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 387, core1 := 1110, core2 := 3, opn := 0 }. -/
theorem F34S_c3_k6 : checkChunkS 3 (L6.F2.diagOf 3) L6.F2.Data.cells_c3 single_3 links_3 pass_3 open43
    [("059204b512e177a4", L6.Certs.C059204b512e177a4), ("05bf22ee20141b09", L6.Certs.C05bf22ee20141b09), ("07018856a1764b34", L6.Certs.C07018856a1764b34), ("07242f678e81f55c", L6.Certs.C07242f678e81f55c), ("1154f63f4ae46ba1", L6.Certs.C1154f63f4ae46ba1), ("177b52d2d54e4b01", L6.Certs.C177b52d2d54e4b01), ("1a140fd715c8977d", L6.Certs.C1a140fd715c8977d), ("1e2967b0cae77bfc", L6.Certs.C1e2967b0cae77bfc), ("1fc5829f7e64f575", L6.Certs.C1fc5829f7e64f575), ("21aff3926f57567e", L6.Certs.C21aff3926f57567e), ("2609698da6259546", L6.Certs.C2609698da6259546), ("27b7c036daadb8d7", L6.Certs.C27b7c036daadb8d7), ("28bd5f3910159820", L6.Certs.C28bd5f3910159820), ("2fc74d4784f04bdc", L6.Certs.C2fc74d4784f04bdc), ("391c3c7fc731914e", L6.Certs.C391c3c7fc731914e), ("3c01e156ee5de7c4", L6.Certs.C3c01e156ee5de7c4), ("3e295c2451418f87", L6.Certs.C3e295c2451418f87), ("44cb11ddbf22c8c7", L6.Certs.C44cb11ddbf22c8c7), ("493681a192bc06ca", L6.Certs.C493681a192bc06ca), ("4eedbedb34ed9102", L6.Certs.C4eedbedb34ed9102), ("5038acf7c79a60be", L6.Certs.C5038acf7c79a60be), ("523a70a88966a74f", L6.Certs.C523a70a88966a74f), ("534b536c8c5ed01a", L6.Certs.C534b536c8c5ed01a), ("541cb148fdb38933", L6.Certs.C541cb148fdb38933), ("5783079c59a1550b", L6.Certs.C5783079c59a1550b), ("5d00be4fed6c02b8", L6.Certs.C5d00be4fed6c02b8), ("62478f59f01913b0", L6.Certs.C62478f59f01913b0), ("6377753c94c99900", L6.Certs.C6377753c94c99900), ("6387869e3a9615e0", L6.Certs.C6387869e3a9615e0), ("6451939f227eb79b", L6.Certs.C6451939f227eb79b), ("679323c60894051f", L6.Certs.C679323c60894051f), ("69425143f6838587", L6.Certs.C69425143f6838587), ("699d11d871de775a", L6.Certs.C699d11d871de775a), ("6ab714f4d84692a6", L6.Certs.C6ab714f4d84692a6), ("6c5e96bff34ebc16", L6.Certs.C6c5e96bff34ebc16), ("6cb81b64dfa2ff3a", L6.Certs.C6cb81b64dfa2ff3a), ("7437b7380293085a", L6.Certs.C7437b7380293085a), ("75077c3232d28783", L6.Certs.C75077c3232d28783), ("7f10f1f3767082da", L6.Certs.C7f10f1f3767082da), ("840c82e8ce38adf2", L6.Certs.C840c82e8ce38adf2), ("842183a5e7ad2f00", L6.Certs.C842183a5e7ad2f00), ("84e3ce8fdc777ad7", L6.Certs.C84e3ce8fdc777ad7), ("88c3ca1abda77158", L6.Certs.C88c3ca1abda77158), ("897da59625543f7b", L6.Certs.C897da59625543f7b), ("8b7828b5e04dab19", L6.Certs.C8b7828b5e04dab19), ("8bbe78015a3100aa", L6.Certs.C8bbe78015a3100aa), ("8e65bfc835be8eb5", L6.Certs.C8e65bfc835be8eb5), ("90aad8bec4c0fe2e", L6.Certs.C90aad8bec4c0fe2e), ("90b15a7e7c4e4eb3", L6.Certs.C90b15a7e7c4e4eb3), ("91187e8d7dfeee9b", L6.Certs.C91187e8d7dfeee9b), ("913a22eee130223e", L6.Certs.C913a22eee130223e), ("96961b1def74ebc2", L6.Certs.C96961b1def74ebc2), ("98575e8f84629ff1", L6.Certs.C98575e8f84629ff1), ("9aca347471741b84", L6.Certs.C9aca347471741b84), ("9b5bed43783c5f61", L6.Certs.C9b5bed43783c5f61), ("9ff5f6dec2baab1d", L6.Certs.C9ff5f6dec2baab1d), ("a03049e6b247dba6", L6.Certs.Ca03049e6b247dba6), ("a354a82d8fa692c1", L6.Certs.Ca354a82d8fa692c1), ("a65a37706335f71b", L6.Certs.Ca65a37706335f71b), ("a7a5827ea915ed3e", L6.Certs.Ca7a5827ea915ed3e), ("ae2ab36ffe129341", L6.Certs.Cae2ab36ffe129341), ("b6efb92403750ecd", L6.Certs.Cb6efb92403750ecd), ("bece27e87a1bd47a", L6.Certs.Cbece27e87a1bd47a), ("c141c278d23fd57b", L6.Certs.Cc141c278d23fd57b), ("c455eb28dd8b707c", L6.Certs.Cc455eb28dd8b707c), ("c4cc46eaa79216c8", L6.Certs.Cc4cc46eaa79216c8), ("c78dafe01015e669", L6.Certs.Cc78dafe01015e669), ("ce07296cae588c90", L6.Certs.Cce07296cae588c90), ("d399a12f11dfae38", L6.Certs.Cd399a12f11dfae38), ("d636f830987946d9", L6.Certs.Cd636f830987946d9), ("dd7f886d75662f5a", L6.Certs.Cdd7f886d75662f5a), ("e20b0e5d198f78df", L6.Certs.Ce20b0e5d198f78df), ("e27952f8372676c2", L6.Certs.Ce27952f8372676c2), ("e36e575c21c81dd7", L6.Certs.Ce36e575c21c81dd7), ("e3e8d223b87fe872", L6.Certs.Ce3e8d223b87fe872), ("e484fe3d072232cf", L6.Certs.Ce484fe3d072232cf), ("e8dd97920792318b", L6.Certs.Ce8dd97920792318b), ("ec3b06053a4dea2f", L6.Certs.Cec3b06053a4dea2f), ("ecdc3c4e37764455", L6.Certs.Cecdc3c4e37764455), ("ed82aeeb929ba915", L6.Certs.Ced82aeeb929ba915), ("f21024ebbab7964d", L6.Certs.Cf21024ebbab7964d), ("f6344910dd62038d", L6.Certs.Cf6344910dd62038d), ("f9d89ba1685be5ab", L6.Certs.Cf9d89ba1685be5ab)]
    9000 10500 { single := 387, core1 := 1110, core2 := 3, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
