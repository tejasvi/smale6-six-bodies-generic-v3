import L6F34.Check
import L6Check.F34.Data.Common
import L6Check.F34.Data.C148
import L6Check.Certs.C0047d1cbcae52699
import L6Check.Certs.C024c10a6c0813828
import L6Check.Certs.C03724b5bd5011f0a
import L6Check.Certs.C05eae2fdc1df6079
import L6Check.Certs.C0d84218e6efa3052
import L6Check.Certs.C119400539ca1b0b5
import L6Check.Certs.C1340a3de36e54646
import L6Check.Certs.C15617350d777485d
import L6Check.Certs.C17da47d0e95136c7
import L6Check.Certs.C1f20b9066e9a6fb3
import L6Check.Certs.C1f60549ed4aa15cf
import L6Check.Certs.C236658e7435c4248
import L6Check.Certs.C28dc4fcc8cc9b7f6
import L6Check.Certs.C2a17efe89ecdafb8
import L6Check.Certs.C2aa7550ef72c758e
import L6Check.Certs.C2d8f5c90504360d8
import L6Check.Certs.C32f853b0132c9622
import L6Check.Certs.C362793ab65c827f6
import L6Check.Certs.C37e96d2833978eee
import L6Check.Certs.C3820fb3b3774ca33
import L6Check.Certs.C392aea6662b7eaef
import L6Check.Certs.C3ca9e7b3ada442ed
import L6Check.Certs.C433e02cba79b9834
import L6Check.Certs.C47ecb03a85136af9
import L6Check.Certs.C49299139d24770e1
import L6Check.Certs.C4b3d156e06797a24
import L6Check.Certs.C509f7c209cf80b4d
import L6Check.Certs.C5783f922e65f69eb
import L6Check.Certs.C5f5101960f4ef24c
import L6Check.Certs.C619cbdd1f991b7f1
import L6Check.Certs.C62ee17b87a21a4a6
import L6Check.Certs.C64032eea1821e565
import L6Check.Certs.C672aeb0321a50384
import L6Check.Certs.C724a7accb412014a
import L6Check.Certs.C7804cfdfea758509
import L6Check.Certs.C7a279a1af6eefd6a
import L6Check.Certs.C7b7c4cbaec9de9fe
import L6Check.Certs.C80dc6294a3a091ea
import L6Check.Certs.C87613b70cdca5dfc
import L6Check.Certs.C87646cfb8291a9c0
import L6Check.Certs.C89c8dbcf57443c09
import L6Check.Certs.C8f89d9164fbf5c6a
import L6Check.Certs.C91863a1535398a0a
import L6Check.Certs.C99430ea8608aaf3d
import L6Check.Certs.Ca520cec9a3210ed0
import L6Check.Certs.Ca68007986617d8f2
import L6Check.Certs.Ca8fcb10e07ed24f4
import L6Check.Certs.Ca93be50c801ce28e
import L6Check.Certs.Cad26c6b6346da7fa
import L6Check.Certs.Caf0cf3972de7db47
import L6Check.Certs.Cb23daeafafb3e010
import L6Check.Certs.Cbd3f2204d9517b24
import L6Check.Certs.Cbda63b1c3bf83f47
import L6Check.Certs.Cbdbf98ba0118b6c7
import L6Check.Certs.Cbf1c1072d313dea1
import L6Check.Certs.Cc0692fe6a8887c6c
import L6Check.Certs.Cc10f282432272633
import L6Check.Certs.Cc2b42efea5c9995c
import L6Check.Certs.Cc423f02ddcf0a15b
import L6Check.Certs.Ccf2c54500d309627
import L6Check.Certs.Cd2fb9b6e3a68a97b
import L6Check.Certs.Cd58c2739d1f6d5ce
import L6Check.Certs.Cd5db2898309b0b61
import L6Check.Certs.Cddaf4bea1fd45916
import L6Check.Certs.Ce132683508dd021a
import L6Check.Certs.Ce1e2aa2612fb03ad
import L6Check.Certs.Ce47a83ddaf16af2f
import L6Check.Certs.Cefddd8b4a3c57d3d
import L6Check.Certs.Cf2282a33e336512f
import L6Check.Certs.Cf6ab40d38d7bb9f6
import L6Check.Certs.Cf6af070559804413
import L6Check.Certs.Cf93d7d3ae1365152

/-! F3/F4 (Proposition 5.3), class 148, cells 0 ≤ cell < 1500 of `data/cells/c148.jsonl`. -/

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

-- the evaluation allocates (parsing the certificates), which counts towards the heartbeats
set_option maxHeartbeats 0 in
/-- Every cell `0 ≤ cell < 1500` of class 148 is excluded by a single term (Lemma 5.1, certified), or
its core polynomials are the initial forms of the cell and the generators of the named certificate
(Lemma 5.2), or it is one of the 43 open cells; with the counts { single := 504, core1 := 996, core2 := 0, opn := 0 }. -/
theorem F34_c148_k0 : checkChunk 148 n6 cells_148 single_148 links_148 pass_148 open43
    [("0047d1cbcae52699", L6.Certs.C0047d1cbcae52699), ("024c10a6c0813828", L6.Certs.C024c10a6c0813828), ("03724b5bd5011f0a", L6.Certs.C03724b5bd5011f0a), ("05eae2fdc1df6079", L6.Certs.C05eae2fdc1df6079), ("0d84218e6efa3052", L6.Certs.C0d84218e6efa3052), ("119400539ca1b0b5", L6.Certs.C119400539ca1b0b5), ("1340a3de36e54646", L6.Certs.C1340a3de36e54646), ("15617350d777485d", L6.Certs.C15617350d777485d), ("17da47d0e95136c7", L6.Certs.C17da47d0e95136c7), ("1f20b9066e9a6fb3", L6.Certs.C1f20b9066e9a6fb3), ("1f60549ed4aa15cf", L6.Certs.C1f60549ed4aa15cf), ("236658e7435c4248", L6.Certs.C236658e7435c4248), ("28dc4fcc8cc9b7f6", L6.Certs.C28dc4fcc8cc9b7f6), ("2a17efe89ecdafb8", L6.Certs.C2a17efe89ecdafb8), ("2aa7550ef72c758e", L6.Certs.C2aa7550ef72c758e), ("2d8f5c90504360d8", L6.Certs.C2d8f5c90504360d8), ("32f853b0132c9622", L6.Certs.C32f853b0132c9622), ("362793ab65c827f6", L6.Certs.C362793ab65c827f6), ("37e96d2833978eee", L6.Certs.C37e96d2833978eee), ("3820fb3b3774ca33", L6.Certs.C3820fb3b3774ca33), ("392aea6662b7eaef", L6.Certs.C392aea6662b7eaef), ("3ca9e7b3ada442ed", L6.Certs.C3ca9e7b3ada442ed), ("433e02cba79b9834", L6.Certs.C433e02cba79b9834), ("47ecb03a85136af9", L6.Certs.C47ecb03a85136af9), ("49299139d24770e1", L6.Certs.C49299139d24770e1), ("4b3d156e06797a24", L6.Certs.C4b3d156e06797a24), ("509f7c209cf80b4d", L6.Certs.C509f7c209cf80b4d), ("5783f922e65f69eb", L6.Certs.C5783f922e65f69eb), ("5f5101960f4ef24c", L6.Certs.C5f5101960f4ef24c), ("619cbdd1f991b7f1", L6.Certs.C619cbdd1f991b7f1), ("62ee17b87a21a4a6", L6.Certs.C62ee17b87a21a4a6), ("64032eea1821e565", L6.Certs.C64032eea1821e565), ("672aeb0321a50384", L6.Certs.C672aeb0321a50384), ("724a7accb412014a", L6.Certs.C724a7accb412014a), ("7804cfdfea758509", L6.Certs.C7804cfdfea758509), ("7a279a1af6eefd6a", L6.Certs.C7a279a1af6eefd6a), ("7b7c4cbaec9de9fe", L6.Certs.C7b7c4cbaec9de9fe), ("80dc6294a3a091ea", L6.Certs.C80dc6294a3a091ea), ("87613b70cdca5dfc", L6.Certs.C87613b70cdca5dfc), ("87646cfb8291a9c0", L6.Certs.C87646cfb8291a9c0), ("89c8dbcf57443c09", L6.Certs.C89c8dbcf57443c09), ("8f89d9164fbf5c6a", L6.Certs.C8f89d9164fbf5c6a), ("91863a1535398a0a", L6.Certs.C91863a1535398a0a), ("99430ea8608aaf3d", L6.Certs.C99430ea8608aaf3d), ("a520cec9a3210ed0", L6.Certs.Ca520cec9a3210ed0), ("a68007986617d8f2", L6.Certs.Ca68007986617d8f2), ("a8fcb10e07ed24f4", L6.Certs.Ca8fcb10e07ed24f4), ("a93be50c801ce28e", L6.Certs.Ca93be50c801ce28e), ("ad26c6b6346da7fa", L6.Certs.Cad26c6b6346da7fa), ("af0cf3972de7db47", L6.Certs.Caf0cf3972de7db47), ("b23daeafafb3e010", L6.Certs.Cb23daeafafb3e010), ("bd3f2204d9517b24", L6.Certs.Cbd3f2204d9517b24), ("bda63b1c3bf83f47", L6.Certs.Cbda63b1c3bf83f47), ("bdbf98ba0118b6c7", L6.Certs.Cbdbf98ba0118b6c7), ("bf1c1072d313dea1", L6.Certs.Cbf1c1072d313dea1), ("c0692fe6a8887c6c", L6.Certs.Cc0692fe6a8887c6c), ("c10f282432272633", L6.Certs.Cc10f282432272633), ("c2b42efea5c9995c", L6.Certs.Cc2b42efea5c9995c), ("c423f02ddcf0a15b", L6.Certs.Cc423f02ddcf0a15b), ("cf2c54500d309627", L6.Certs.Ccf2c54500d309627), ("d2fb9b6e3a68a97b", L6.Certs.Cd2fb9b6e3a68a97b), ("d58c2739d1f6d5ce", L6.Certs.Cd58c2739d1f6d5ce), ("d5db2898309b0b61", L6.Certs.Cd5db2898309b0b61), ("ddaf4bea1fd45916", L6.Certs.Cddaf4bea1fd45916), ("e132683508dd021a", L6.Certs.Ce132683508dd021a), ("e1e2aa2612fb03ad", L6.Certs.Ce1e2aa2612fb03ad), ("e47a83ddaf16af2f", L6.Certs.Ce47a83ddaf16af2f), ("efddd8b4a3c57d3d", L6.Certs.Cefddd8b4a3c57d3d), ("f2282a33e336512f", L6.Certs.Cf2282a33e336512f), ("f6ab40d38d7bb9f6", L6.Certs.Cf6ab40d38d7bb9f6), ("f6af070559804413", L6.Certs.Cf6af070559804413), ("f93d7d3ae1365152", L6.Certs.Cf93d7d3ae1365152)]
    0 1500 { single := 504, core1 := 996, core2 := 0, opn := 0 } = true := by
  native_decide

end L6.F34.Checks
