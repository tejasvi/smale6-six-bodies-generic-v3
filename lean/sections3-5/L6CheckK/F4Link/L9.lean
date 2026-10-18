import L6SoundK.F4.Link
import L6Check.Certs.C4f50077be127130e
import L6Check.Certs.C4f7138cb286daef3
import L6Check.Certs.C4f738a6a99fb6160
import L6Check.Certs.C4fa8fda48a8d4fe8
import L6Check.Certs.C500511c37e82f8b6
import L6Check.Certs.C5017dd3d26ef0fa7
import L6Check.Certs.C5038acf7c79a60be
import L6Check.Certs.C50735654eebf54fe
import L6Check.Certs.C508fa2210e538bd7
import L6Check.Certs.C509f7c209cf80b4d
import L6Check.Certs.C50c069c45ab6a94b
import L6Check.Certs.C50dc0c810be99916
import L6Check.Certs.C50febf9a411e6527
import L6Check.Certs.C510cd38a096e77e7
import L6Check.Certs.C51325aff203d7aed
import L6Check.Certs.C5153937293409a35
import L6Check.Certs.C5196a2dbba6aed97
import L6Check.Certs.C51a136f020a20690
import L6Check.Certs.C51da5223ba20151f
import L6Check.Certs.C51ee843597cff9f3
import L6Check.Certs.C522c83b2bdf35607
import L6Check.Certs.C523a70a88966a74f
import L6Check.Certs.C52699eba3dd58593
import L6Check.Certs.C52709fbc0a12e485
import L6Check.Certs.C52cd84399cd40c05
import L6Check.Certs.C52cf87e3babff2d7
import L6Check.Certs.C52dc1e65ab448a9c
import L6Check.Certs.C531bc2c54bb82726
import L6Check.Certs.C531f1608213f8f5e
import L6Check.Certs.C5323dbfec5dccf4f
import L6Check.Certs.C534b536c8c5ed01a
import L6Check.Certs.C5353fad283bd1fe9
import L6Check.Certs.C5380c10c49621d0a
import L6Check.Certs.C53c8b2ddab2b632b
import L6Check.Certs.C53de25baa06ae77e
import L6Check.Certs.C53deb1e55eab591b
import L6Check.Certs.C541cb148fdb38933
import L6Check.Certs.C541d72646552e387
import L6Check.Certs.C542a76355417fd47
import L6Check.Certs.C5437d1ed83271756
import L6Check.Certs.C54483d807bd4f917
import L6Check.Certs.C544c7022c2b3939c
import L6Check.Certs.C546c25f5006cdb1e
import L6Check.Certs.C549547755e1f7a45
import L6Check.Certs.C54dd9b1d97c5f4ff
import L6Check.Certs.C54e9bfbed9063e83
import L6Check.Certs.C55290219a6343391
import L6Check.Certs.C553a98a51c8385e5
import L6Check.Certs.C553c67900281f55f
import L6Check.Certs.C558e59d95895105f
import L6Check.Certs.C55e062bc9697ab2e
import L6Check.Certs.C56053a1b4afdd71c
import L6Check.Certs.C563b78814b60f91a
import L6Check.Certs.C5666f51eb41b85c3
import L6Check.Certs.C5693445944ae1e34
import L6Check.Certs.C56e4849a55cd0392
import L6Check.Certs.C5701e0a62003d460
import L6Check.Certs.C57184cd72518fed4
import L6Check.Certs.C5734369cab42a80d
import L6Check.Certs.C5783079c59a1550b
import L6Check.Certs.C5783f922e65f69eb
import L6Check.Certs.C57b00b6081bb0cf0
import L6Check.Certs.C57b1bef2cd072552
import L6Check.Certs.C57c2b2f3ce64f2cc
import L6CheckK.F4.P47
import L6CheckK.F4.M9
import L6CheckK.F4.P48
import L6CheckK.F4.P49
import L6CheckK.F4.P50
import L6CheckK.F4.P51
import L6CheckK.F4.C53deb1e55eab591b.Data
import L6CheckK.F4.P52
import L6CheckK.F4.P53
import L6CheckK.F4.C553c67900281f55f.Data
import L6CheckK.F4.P54
import L6CheckK.F4.P55

set_option maxHeartbeats 0
-- the decidability instance of the 4-tuple equality is larger than the default bound
set_option synthInstance.maxSize 1024

/-! Links of the certificate texts to the literal certificates, certificates 576–639. -/

namespace L6CheckK.F4Link

open L6.Poly

theorem link_4f50077be127130e : (parseCert L6.Certs.C4f50077be127130e).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C4f50077be127130e.certH.nvar, L6CheckK.F4.C4f50077be127130e.certH.fixed, L6CheckK.F4.C4f50077be127130e.certH.gens, L6CheckK.F4.C4f50077be127130e.certH.h) := by native_decide
theorem meaning_4f50077be127130e : ∃ c, parseCert L6.Certs.C4f50077be127130e = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_4f50077be127130e L6CheckK.F4.C4f50077be127130e.cert
theorem link_4f7138cb286daef3 : (parseCert L6.Certs.C4f7138cb286daef3).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C4f7138cb286daef3.certH.nvar, L6CheckK.F4.C4f7138cb286daef3.certH.fixed, L6CheckK.F4.C4f7138cb286daef3.certH.gens, L6CheckK.F4.C4f7138cb286daef3.certH.h) := by native_decide
theorem meaning_4f7138cb286daef3 : ∃ c, parseCert L6.Certs.C4f7138cb286daef3 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_4f7138cb286daef3 L6CheckK.F4.C4f7138cb286daef3.cert
theorem link_4f738a6a99fb6160 : (parseCert L6.Certs.C4f738a6a99fb6160).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C4f738a6a99fb6160.certH.nvar, L6CheckK.F4.C4f738a6a99fb6160.certH.fixed, L6CheckK.F4.C4f738a6a99fb6160.certH.gens, L6CheckK.F4.C4f738a6a99fb6160.certH.h) := by native_decide
theorem meaning_4f738a6a99fb6160 : ∃ c, parseCert L6.Certs.C4f738a6a99fb6160 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_4f738a6a99fb6160 L6CheckK.F4.C4f738a6a99fb6160.cert
theorem link_4fa8fda48a8d4fe8 : (parseCert L6.Certs.C4fa8fda48a8d4fe8).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C4fa8fda48a8d4fe8.certH.nvar, L6CheckK.F4.C4fa8fda48a8d4fe8.certH.fixed, L6CheckK.F4.C4fa8fda48a8d4fe8.certH.gens, L6CheckK.F4.C4fa8fda48a8d4fe8.certH.h) := by native_decide
theorem meaning_4fa8fda48a8d4fe8 : ∃ c, parseCert L6.Certs.C4fa8fda48a8d4fe8 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_4fa8fda48a8d4fe8 L6CheckK.F4.C4fa8fda48a8d4fe8.cert
theorem link_500511c37e82f8b6 : (parseCert L6.Certs.C500511c37e82f8b6).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C500511c37e82f8b6.certH.nvar, L6CheckK.F4.C500511c37e82f8b6.certH.fixed, L6CheckK.F4.C500511c37e82f8b6.certH.gens, L6CheckK.F4.C500511c37e82f8b6.certH.h) := by native_decide
theorem meaning_500511c37e82f8b6 : ∃ c, parseCert L6.Certs.C500511c37e82f8b6 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_500511c37e82f8b6 L6CheckK.F4.C500511c37e82f8b6.cert
theorem link_5017dd3d26ef0fa7 : (parseCert L6.Certs.C5017dd3d26ef0fa7).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5017dd3d26ef0fa7.certH.nvar, L6CheckK.F4.C5017dd3d26ef0fa7.certH.fixed, L6CheckK.F4.C5017dd3d26ef0fa7.certH.gens, L6CheckK.F4.C5017dd3d26ef0fa7.certH.h) := by native_decide
theorem meaning_5017dd3d26ef0fa7 : ∃ c, parseCert L6.Certs.C5017dd3d26ef0fa7 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5017dd3d26ef0fa7 L6CheckK.F4.C5017dd3d26ef0fa7.cert
theorem link_5038acf7c79a60be : (parseCert L6.Certs.C5038acf7c79a60be).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5038acf7c79a60be.certH.nvar, L6CheckK.F4.C5038acf7c79a60be.certH.fixed, L6CheckK.F4.C5038acf7c79a60be.certH.gens, L6CheckK.F4.C5038acf7c79a60be.certH.h) := by native_decide
theorem meaning_5038acf7c79a60be : ∃ c, parseCert L6.Certs.C5038acf7c79a60be = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5038acf7c79a60be L6CheckK.F4.C5038acf7c79a60be.cert
theorem link_50735654eebf54fe : (parseCert L6.Certs.C50735654eebf54fe).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C50735654eebf54fe.certH.nvar, L6CheckK.F4.C50735654eebf54fe.certH.fixed, L6CheckK.F4.C50735654eebf54fe.certH.gens, L6CheckK.F4.C50735654eebf54fe.certH.h) := by native_decide
theorem meaning_50735654eebf54fe : ∃ c, parseCert L6.Certs.C50735654eebf54fe = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_50735654eebf54fe L6CheckK.F4.C50735654eebf54fe.cert
theorem link_508fa2210e538bd7 : (parseCert L6.Certs.C508fa2210e538bd7).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C508fa2210e538bd7.certH.nvar, L6CheckK.F4.C508fa2210e538bd7.certH.fixed, L6CheckK.F4.C508fa2210e538bd7.certH.gens, L6CheckK.F4.C508fa2210e538bd7.certH.h) := by native_decide
theorem meaning_508fa2210e538bd7 : ∃ c, parseCert L6.Certs.C508fa2210e538bd7 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_508fa2210e538bd7 L6CheckK.F4.C508fa2210e538bd7.cert
theorem link_509f7c209cf80b4d : (parseCert L6.Certs.C509f7c209cf80b4d).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C509f7c209cf80b4d.certH.nvar, L6CheckK.F4.C509f7c209cf80b4d.certH.fixed, L6CheckK.F4.C509f7c209cf80b4d.certH.gens, L6CheckK.F4.C509f7c209cf80b4d.certH.h) := by native_decide
theorem meaning_509f7c209cf80b4d : ∃ c, parseCert L6.Certs.C509f7c209cf80b4d = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_509f7c209cf80b4d L6CheckK.F4.C509f7c209cf80b4d.cert
theorem link_50c069c45ab6a94b : (parseCert L6.Certs.C50c069c45ab6a94b).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C50c069c45ab6a94b.certH.nvar, L6CheckK.F4.C50c069c45ab6a94b.certH.fixed, L6CheckK.F4.C50c069c45ab6a94b.certH.gens, L6CheckK.F4.C50c069c45ab6a94b.certH.h) := by native_decide
theorem meaning_50c069c45ab6a94b : ∃ c, parseCert L6.Certs.C50c069c45ab6a94b = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_50c069c45ab6a94b L6CheckK.F4.C50c069c45ab6a94b.cert
theorem link_50dc0c810be99916 : (parseCert L6.Certs.C50dc0c810be99916).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C50dc0c810be99916.certH.nvar, L6CheckK.F4.C50dc0c810be99916.certH.fixed, L6CheckK.F4.C50dc0c810be99916.certH.gens, L6CheckK.F4.C50dc0c810be99916.certH.h) := by native_decide
theorem meaning_50dc0c810be99916 : ∃ c, parseCert L6.Certs.C50dc0c810be99916 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_50dc0c810be99916 L6CheckK.F4.C50dc0c810be99916.cert
theorem link_50febf9a411e6527 : (parseCert L6.Certs.C50febf9a411e6527).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C50febf9a411e6527.certH.nvar, L6CheckK.F4.C50febf9a411e6527.certH.fixed, L6CheckK.F4.C50febf9a411e6527.certH.gens, L6CheckK.F4.C50febf9a411e6527.certH.h) := by native_decide
theorem meaning_50febf9a411e6527 : ∃ c, parseCert L6.Certs.C50febf9a411e6527 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_50febf9a411e6527 L6CheckK.F4.C50febf9a411e6527.cert
theorem link_510cd38a096e77e7 : (parseCert L6.Certs.C510cd38a096e77e7).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C510cd38a096e77e7.certH.nvar, L6CheckK.F4.C510cd38a096e77e7.certH.fixed, L6CheckK.F4.C510cd38a096e77e7.certH.gens, L6CheckK.F4.C510cd38a096e77e7.certH.h) := by native_decide
theorem meaning_510cd38a096e77e7 : ∃ c, parseCert L6.Certs.C510cd38a096e77e7 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_510cd38a096e77e7 L6CheckK.F4.C510cd38a096e77e7.cert
theorem link_51325aff203d7aed : (parseCert L6.Certs.C51325aff203d7aed).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C51325aff203d7aed.certH.nvar, L6CheckK.F4.C51325aff203d7aed.certH.fixed, L6CheckK.F4.C51325aff203d7aed.certH.gens, L6CheckK.F4.C51325aff203d7aed.certH.h) := by native_decide
theorem meaning_51325aff203d7aed : ∃ c, parseCert L6.Certs.C51325aff203d7aed = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_51325aff203d7aed L6CheckK.F4.C51325aff203d7aed.cert
theorem link_5153937293409a35 : (parseCert L6.Certs.C5153937293409a35).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5153937293409a35.certH.nvar, L6CheckK.F4.C5153937293409a35.certH.fixed, L6CheckK.F4.C5153937293409a35.certH.gens, L6CheckK.F4.C5153937293409a35.certH.h) := by native_decide
theorem meaning_5153937293409a35 : ∃ c, parseCert L6.Certs.C5153937293409a35 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5153937293409a35 L6CheckK.F4.C5153937293409a35.cert
theorem link_5196a2dbba6aed97 : (parseCert L6.Certs.C5196a2dbba6aed97).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5196a2dbba6aed97.certH.nvar, L6CheckK.F4.C5196a2dbba6aed97.certH.fixed, L6CheckK.F4.C5196a2dbba6aed97.certH.gens, L6CheckK.F4.C5196a2dbba6aed97.certH.h) := by native_decide
theorem meaning_5196a2dbba6aed97 : ∃ c, parseCert L6.Certs.C5196a2dbba6aed97 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5196a2dbba6aed97 L6CheckK.F4.C5196a2dbba6aed97.cert
theorem link_51a136f020a20690 : (parseCert L6.Certs.C51a136f020a20690).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C51a136f020a20690.certH.nvar, L6CheckK.F4.C51a136f020a20690.certH.fixed, L6CheckK.F4.C51a136f020a20690.certH.gens, L6CheckK.F4.C51a136f020a20690.certH.h) := by native_decide
theorem meaning_51a136f020a20690 : ∃ c, parseCert L6.Certs.C51a136f020a20690 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_51a136f020a20690 L6CheckK.F4.C51a136f020a20690.cert
theorem link_51da5223ba20151f : (parseCert L6.Certs.C51da5223ba20151f).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C51da5223ba20151f.certH.nvar, L6CheckK.F4.C51da5223ba20151f.certH.fixed, L6CheckK.F4.C51da5223ba20151f.certH.gens, L6CheckK.F4.C51da5223ba20151f.certH.h) := by native_decide
theorem meaning_51da5223ba20151f : ∃ c, parseCert L6.Certs.C51da5223ba20151f = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_51da5223ba20151f L6CheckK.F4.C51da5223ba20151f.cert
theorem link_51ee843597cff9f3 : (parseCert L6.Certs.C51ee843597cff9f3).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C51ee843597cff9f3.certH.nvar, L6CheckK.F4.C51ee843597cff9f3.certH.fixed, L6CheckK.F4.C51ee843597cff9f3.certH.gens, L6CheckK.F4.C51ee843597cff9f3.certH.h) := by native_decide
theorem meaning_51ee843597cff9f3 : ∃ c, parseCert L6.Certs.C51ee843597cff9f3 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_51ee843597cff9f3 L6CheckK.F4.C51ee843597cff9f3.cert
theorem link_522c83b2bdf35607 : (parseCert L6.Certs.C522c83b2bdf35607).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C522c83b2bdf35607.certH.nvar, L6CheckK.F4.C522c83b2bdf35607.certH.fixed, L6CheckK.F4.C522c83b2bdf35607.certH.gens, L6CheckK.F4.C522c83b2bdf35607.certH.h) := by native_decide
theorem meaning_522c83b2bdf35607 : ∃ c, parseCert L6.Certs.C522c83b2bdf35607 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_522c83b2bdf35607 L6CheckK.F4.C522c83b2bdf35607.cert
theorem link_523a70a88966a74f : (parseCert L6.Certs.C523a70a88966a74f).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C523a70a88966a74f.certH.nvar, L6CheckK.F4.C523a70a88966a74f.certH.fixed, L6CheckK.F4.C523a70a88966a74f.certH.gens, L6CheckK.F4.C523a70a88966a74f.certH.h) := by native_decide
theorem meaning_523a70a88966a74f : ∃ c, parseCert L6.Certs.C523a70a88966a74f = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_523a70a88966a74f L6CheckK.F4.C523a70a88966a74f.cert
theorem link_52699eba3dd58593 : (parseCert L6.Certs.C52699eba3dd58593).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C52699eba3dd58593.certH.nvar, L6CheckK.F4.C52699eba3dd58593.certH.fixed, L6CheckK.F4.C52699eba3dd58593.certH.gens, L6CheckK.F4.C52699eba3dd58593.certH.h) := by native_decide
theorem meaning_52699eba3dd58593 : ∃ c, parseCert L6.Certs.C52699eba3dd58593 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_52699eba3dd58593 L6CheckK.F4.C52699eba3dd58593.cert
theorem link_52709fbc0a12e485 : (parseCert L6.Certs.C52709fbc0a12e485).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C52709fbc0a12e485.certH.nvar, L6CheckK.F4.C52709fbc0a12e485.certH.fixed, L6CheckK.F4.C52709fbc0a12e485.certH.gens, L6CheckK.F4.C52709fbc0a12e485.certH.h) := by native_decide
theorem meaning_52709fbc0a12e485 : ∃ c, parseCert L6.Certs.C52709fbc0a12e485 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_52709fbc0a12e485 L6CheckK.F4.C52709fbc0a12e485.cert
theorem link_52cd84399cd40c05 : (parseCert L6.Certs.C52cd84399cd40c05).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C52cd84399cd40c05.certH.nvar, L6CheckK.F4.C52cd84399cd40c05.certH.fixed, L6CheckK.F4.C52cd84399cd40c05.certH.gens, L6CheckK.F4.C52cd84399cd40c05.certH.h) := by native_decide
theorem meaning_52cd84399cd40c05 : ∃ c, parseCert L6.Certs.C52cd84399cd40c05 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_52cd84399cd40c05 L6CheckK.F4.C52cd84399cd40c05.cert
theorem link_52cf87e3babff2d7 : (parseCert L6.Certs.C52cf87e3babff2d7).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C52cf87e3babff2d7.certH.nvar, L6CheckK.F4.C52cf87e3babff2d7.certH.fixed, L6CheckK.F4.C52cf87e3babff2d7.certH.gens, L6CheckK.F4.C52cf87e3babff2d7.certH.h) := by native_decide
theorem meaning_52cf87e3babff2d7 : ∃ c, parseCert L6.Certs.C52cf87e3babff2d7 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_52cf87e3babff2d7 L6CheckK.F4.C52cf87e3babff2d7.cert
theorem link_52dc1e65ab448a9c : (parseCert L6.Certs.C52dc1e65ab448a9c).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C52dc1e65ab448a9c.certH.nvar, L6CheckK.F4.C52dc1e65ab448a9c.certH.fixed, L6CheckK.F4.C52dc1e65ab448a9c.certH.gens, L6CheckK.F4.C52dc1e65ab448a9c.certH.h) := by native_decide
theorem meaning_52dc1e65ab448a9c : ∃ c, parseCert L6.Certs.C52dc1e65ab448a9c = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_52dc1e65ab448a9c L6CheckK.F4.C52dc1e65ab448a9c.cert
theorem link_531bc2c54bb82726 : (parseCert L6.Certs.C531bc2c54bb82726).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C531bc2c54bb82726.certH.nvar, L6CheckK.F4.C531bc2c54bb82726.certH.fixed, L6CheckK.F4.C531bc2c54bb82726.certH.gens, L6CheckK.F4.C531bc2c54bb82726.certH.h) := by native_decide
theorem meaning_531bc2c54bb82726 : ∃ c, parseCert L6.Certs.C531bc2c54bb82726 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_531bc2c54bb82726 L6CheckK.F4.C531bc2c54bb82726.cert
theorem link_531f1608213f8f5e : (parseCert L6.Certs.C531f1608213f8f5e).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C531f1608213f8f5e.certH.nvar, L6CheckK.F4.C531f1608213f8f5e.certH.fixed, L6CheckK.F4.C531f1608213f8f5e.certH.gens, L6CheckK.F4.C531f1608213f8f5e.certH.h) := by native_decide
theorem meaning_531f1608213f8f5e : ∃ c, parseCert L6.Certs.C531f1608213f8f5e = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_531f1608213f8f5e L6CheckK.F4.C531f1608213f8f5e.cert
theorem link_5323dbfec5dccf4f : (parseCert L6.Certs.C5323dbfec5dccf4f).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5323dbfec5dccf4f.certH.nvar, L6CheckK.F4.C5323dbfec5dccf4f.certH.fixed, L6CheckK.F4.C5323dbfec5dccf4f.certH.gens, L6CheckK.F4.C5323dbfec5dccf4f.certH.h) := by native_decide
theorem meaning_5323dbfec5dccf4f : ∃ c, parseCert L6.Certs.C5323dbfec5dccf4f = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5323dbfec5dccf4f L6CheckK.F4.C5323dbfec5dccf4f.cert
theorem link_534b536c8c5ed01a : (parseCert L6.Certs.C534b536c8c5ed01a).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C534b536c8c5ed01a.certH.nvar, L6CheckK.F4.C534b536c8c5ed01a.certH.fixed, L6CheckK.F4.C534b536c8c5ed01a.certH.gens, L6CheckK.F4.C534b536c8c5ed01a.certH.h) := by native_decide
theorem meaning_534b536c8c5ed01a : ∃ c, parseCert L6.Certs.C534b536c8c5ed01a = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_534b536c8c5ed01a L6CheckK.F4.C534b536c8c5ed01a.cert
theorem link_5353fad283bd1fe9 : (parseCert L6.Certs.C5353fad283bd1fe9).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5353fad283bd1fe9.certH.nvar, L6CheckK.F4.C5353fad283bd1fe9.certH.fixed, L6CheckK.F4.C5353fad283bd1fe9.certH.gens, L6CheckK.F4.C5353fad283bd1fe9.certH.h) := by native_decide
theorem meaning_5353fad283bd1fe9 : ∃ c, parseCert L6.Certs.C5353fad283bd1fe9 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5353fad283bd1fe9 L6CheckK.F4.C5353fad283bd1fe9.cert
theorem link_5380c10c49621d0a : (parseCert L6.Certs.C5380c10c49621d0a).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5380c10c49621d0a.certH.nvar, L6CheckK.F4.C5380c10c49621d0a.certH.fixed, L6CheckK.F4.C5380c10c49621d0a.certH.gens, L6CheckK.F4.C5380c10c49621d0a.certH.h) := by native_decide
theorem meaning_5380c10c49621d0a : ∃ c, parseCert L6.Certs.C5380c10c49621d0a = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5380c10c49621d0a L6CheckK.F4.C5380c10c49621d0a.cert
theorem link_53c8b2ddab2b632b : (parseCert L6.Certs.C53c8b2ddab2b632b).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C53c8b2ddab2b632b.certH.nvar, L6CheckK.F4.C53c8b2ddab2b632b.certH.fixed, L6CheckK.F4.C53c8b2ddab2b632b.certH.gens, L6CheckK.F4.C53c8b2ddab2b632b.certH.h) := by native_decide
theorem meaning_53c8b2ddab2b632b : ∃ c, parseCert L6.Certs.C53c8b2ddab2b632b = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_53c8b2ddab2b632b L6CheckK.F4.C53c8b2ddab2b632b.cert
theorem link_53de25baa06ae77e : (parseCert L6.Certs.C53de25baa06ae77e).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C53de25baa06ae77e.certH.nvar, L6CheckK.F4.C53de25baa06ae77e.certH.fixed, L6CheckK.F4.C53de25baa06ae77e.certH.gens, L6CheckK.F4.C53de25baa06ae77e.certH.h) := by native_decide
theorem meaning_53de25baa06ae77e : ∃ c, parseCert L6.Certs.C53de25baa06ae77e = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_53de25baa06ae77e L6CheckK.F4.C53de25baa06ae77e.cert
theorem link_53deb1e55eab591b : (parseCert L6.Certs.C53deb1e55eab591b).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C53deb1e55eab591b.certH.nvar, L6CheckK.F4.C53deb1e55eab591b.certH.fixed, L6CheckK.F4.C53deb1e55eab591b.certH.gens, L6CheckK.F4.C53deb1e55eab591b.certH.h) := by native_decide
theorem meaning_53deb1e55eab591b : ∃ c, parseCert L6.Certs.C53deb1e55eab591b = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_53deb1e55eab591b L6CheckK.F4.C53deb1e55eab591b.cert
theorem link_541cb148fdb38933 : (parseCert L6.Certs.C541cb148fdb38933).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C541cb148fdb38933.certH.nvar, L6CheckK.F4.C541cb148fdb38933.certH.fixed, L6CheckK.F4.C541cb148fdb38933.certH.gens, L6CheckK.F4.C541cb148fdb38933.certH.h) := by native_decide
theorem meaning_541cb148fdb38933 : ∃ c, parseCert L6.Certs.C541cb148fdb38933 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_541cb148fdb38933 L6CheckK.F4.C541cb148fdb38933.cert
theorem link_541d72646552e387 : (parseCert L6.Certs.C541d72646552e387).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C541d72646552e387.certH.nvar, L6CheckK.F4.C541d72646552e387.certH.fixed, L6CheckK.F4.C541d72646552e387.certH.gens, L6CheckK.F4.C541d72646552e387.certH.h) := by native_decide
theorem meaning_541d72646552e387 : ∃ c, parseCert L6.Certs.C541d72646552e387 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_541d72646552e387 L6CheckK.F4.C541d72646552e387.cert
theorem link_542a76355417fd47 : (parseCert L6.Certs.C542a76355417fd47).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C542a76355417fd47.certH.nvar, L6CheckK.F4.C542a76355417fd47.certH.fixed, L6CheckK.F4.C542a76355417fd47.certH.gens, L6CheckK.F4.C542a76355417fd47.certH.h) := by native_decide
theorem meaning_542a76355417fd47 : ∃ c, parseCert L6.Certs.C542a76355417fd47 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_542a76355417fd47 L6CheckK.F4.C542a76355417fd47.cert
theorem link_5437d1ed83271756 : (parseCert L6.Certs.C5437d1ed83271756).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5437d1ed83271756.certH.nvar, L6CheckK.F4.C5437d1ed83271756.certH.fixed, L6CheckK.F4.C5437d1ed83271756.certH.gens, L6CheckK.F4.C5437d1ed83271756.certH.h) := by native_decide
theorem meaning_5437d1ed83271756 : ∃ c, parseCert L6.Certs.C5437d1ed83271756 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5437d1ed83271756 L6CheckK.F4.C5437d1ed83271756.cert
theorem link_54483d807bd4f917 : (parseCert L6.Certs.C54483d807bd4f917).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C54483d807bd4f917.certH.nvar, L6CheckK.F4.C54483d807bd4f917.certH.fixed, L6CheckK.F4.C54483d807bd4f917.certH.gens, L6CheckK.F4.C54483d807bd4f917.certH.h) := by native_decide
theorem meaning_54483d807bd4f917 : ∃ c, parseCert L6.Certs.C54483d807bd4f917 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_54483d807bd4f917 L6CheckK.F4.C54483d807bd4f917.cert
theorem link_544c7022c2b3939c : (parseCert L6.Certs.C544c7022c2b3939c).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C544c7022c2b3939c.certH.nvar, L6CheckK.F4.C544c7022c2b3939c.certH.fixed, L6CheckK.F4.C544c7022c2b3939c.certH.gens, L6CheckK.F4.C544c7022c2b3939c.certH.h) := by native_decide
theorem meaning_544c7022c2b3939c : ∃ c, parseCert L6.Certs.C544c7022c2b3939c = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_544c7022c2b3939c L6CheckK.F4.C544c7022c2b3939c.cert
theorem link_546c25f5006cdb1e : (parseCert L6.Certs.C546c25f5006cdb1e).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C546c25f5006cdb1e.certH.nvar, L6CheckK.F4.C546c25f5006cdb1e.certH.fixed, L6CheckK.F4.C546c25f5006cdb1e.certH.gens, L6CheckK.F4.C546c25f5006cdb1e.certH.h) := by native_decide
theorem meaning_546c25f5006cdb1e : ∃ c, parseCert L6.Certs.C546c25f5006cdb1e = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_546c25f5006cdb1e L6CheckK.F4.C546c25f5006cdb1e.cert
theorem link_549547755e1f7a45 : (parseCert L6.Certs.C549547755e1f7a45).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C549547755e1f7a45.certH.nvar, L6CheckK.F4.C549547755e1f7a45.certH.fixed, L6CheckK.F4.C549547755e1f7a45.certH.gens, L6CheckK.F4.C549547755e1f7a45.certH.h) := by native_decide
theorem meaning_549547755e1f7a45 : ∃ c, parseCert L6.Certs.C549547755e1f7a45 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_549547755e1f7a45 L6CheckK.F4.C549547755e1f7a45.cert
theorem link_54dd9b1d97c5f4ff : (parseCert L6.Certs.C54dd9b1d97c5f4ff).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C54dd9b1d97c5f4ff.certH.nvar, L6CheckK.F4.C54dd9b1d97c5f4ff.certH.fixed, L6CheckK.F4.C54dd9b1d97c5f4ff.certH.gens, L6CheckK.F4.C54dd9b1d97c5f4ff.certH.h) := by native_decide
theorem meaning_54dd9b1d97c5f4ff : ∃ c, parseCert L6.Certs.C54dd9b1d97c5f4ff = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_54dd9b1d97c5f4ff L6CheckK.F4.C54dd9b1d97c5f4ff.cert
theorem link_54e9bfbed9063e83 : (parseCert L6.Certs.C54e9bfbed9063e83).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C54e9bfbed9063e83.certH.nvar, L6CheckK.F4.C54e9bfbed9063e83.certH.fixed, L6CheckK.F4.C54e9bfbed9063e83.certH.gens, L6CheckK.F4.C54e9bfbed9063e83.certH.h) := by native_decide
theorem meaning_54e9bfbed9063e83 : ∃ c, parseCert L6.Certs.C54e9bfbed9063e83 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_54e9bfbed9063e83 L6CheckK.F4.C54e9bfbed9063e83.cert
theorem link_55290219a6343391 : (parseCert L6.Certs.C55290219a6343391).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C55290219a6343391.certH.nvar, L6CheckK.F4.C55290219a6343391.certH.fixed, L6CheckK.F4.C55290219a6343391.certH.gens, L6CheckK.F4.C55290219a6343391.certH.h) := by native_decide
theorem meaning_55290219a6343391 : ∃ c, parseCert L6.Certs.C55290219a6343391 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_55290219a6343391 L6CheckK.F4.C55290219a6343391.cert
theorem link_553a98a51c8385e5 : (parseCert L6.Certs.C553a98a51c8385e5).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C553a98a51c8385e5.certH.nvar, L6CheckK.F4.C553a98a51c8385e5.certH.fixed, L6CheckK.F4.C553a98a51c8385e5.certH.gens, L6CheckK.F4.C553a98a51c8385e5.certH.h) := by native_decide
theorem meaning_553a98a51c8385e5 : ∃ c, parseCert L6.Certs.C553a98a51c8385e5 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_553a98a51c8385e5 L6CheckK.F4.C553a98a51c8385e5.cert
theorem link_553c67900281f55f : (parseCert L6.Certs.C553c67900281f55f).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C553c67900281f55f.certH.nvar, L6CheckK.F4.C553c67900281f55f.certH.fixed, L6CheckK.F4.C553c67900281f55f.certH.gens, L6CheckK.F4.C553c67900281f55f.certH.h) := by native_decide
theorem meaning_553c67900281f55f : ∃ c, parseCert L6.Certs.C553c67900281f55f = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_553c67900281f55f L6CheckK.F4.C553c67900281f55f.cert
theorem link_558e59d95895105f : (parseCert L6.Certs.C558e59d95895105f).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C558e59d95895105f.certH.nvar, L6CheckK.F4.C558e59d95895105f.certH.fixed, L6CheckK.F4.C558e59d95895105f.certH.gens, L6CheckK.F4.C558e59d95895105f.certH.h) := by native_decide
theorem meaning_558e59d95895105f : ∃ c, parseCert L6.Certs.C558e59d95895105f = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_558e59d95895105f L6CheckK.F4.C558e59d95895105f.cert
theorem link_55e062bc9697ab2e : (parseCert L6.Certs.C55e062bc9697ab2e).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C55e062bc9697ab2e.certH.nvar, L6CheckK.F4.C55e062bc9697ab2e.certH.fixed, L6CheckK.F4.C55e062bc9697ab2e.certH.gens, L6CheckK.F4.C55e062bc9697ab2e.certH.h) := by native_decide
theorem meaning_55e062bc9697ab2e : ∃ c, parseCert L6.Certs.C55e062bc9697ab2e = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_55e062bc9697ab2e L6CheckK.F4.C55e062bc9697ab2e.cert
theorem link_56053a1b4afdd71c : (parseCert L6.Certs.C56053a1b4afdd71c).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C56053a1b4afdd71c.certH.nvar, L6CheckK.F4.C56053a1b4afdd71c.certH.fixed, L6CheckK.F4.C56053a1b4afdd71c.certH.gens, L6CheckK.F4.C56053a1b4afdd71c.certH.h) := by native_decide
theorem meaning_56053a1b4afdd71c : ∃ c, parseCert L6.Certs.C56053a1b4afdd71c = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_56053a1b4afdd71c L6CheckK.F4.C56053a1b4afdd71c.cert
theorem link_563b78814b60f91a : (parseCert L6.Certs.C563b78814b60f91a).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C563b78814b60f91a.certH.nvar, L6CheckK.F4.C563b78814b60f91a.certH.fixed, L6CheckK.F4.C563b78814b60f91a.certH.gens, L6CheckK.F4.C563b78814b60f91a.certH.h) := by native_decide
theorem meaning_563b78814b60f91a : ∃ c, parseCert L6.Certs.C563b78814b60f91a = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_563b78814b60f91a L6CheckK.F4.C563b78814b60f91a.cert
theorem link_5666f51eb41b85c3 : (parseCert L6.Certs.C5666f51eb41b85c3).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5666f51eb41b85c3.certH.nvar, L6CheckK.F4.C5666f51eb41b85c3.certH.fixed, L6CheckK.F4.C5666f51eb41b85c3.certH.gens, L6CheckK.F4.C5666f51eb41b85c3.certH.h) := by native_decide
theorem meaning_5666f51eb41b85c3 : ∃ c, parseCert L6.Certs.C5666f51eb41b85c3 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5666f51eb41b85c3 L6CheckK.F4.C5666f51eb41b85c3.cert
theorem link_5693445944ae1e34 : (parseCert L6.Certs.C5693445944ae1e34).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5693445944ae1e34.certH.nvar, L6CheckK.F4.C5693445944ae1e34.certH.fixed, L6CheckK.F4.C5693445944ae1e34.certH.gens, L6CheckK.F4.C5693445944ae1e34.certH.h) := by native_decide
theorem meaning_5693445944ae1e34 : ∃ c, parseCert L6.Certs.C5693445944ae1e34 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5693445944ae1e34 L6CheckK.F4.C5693445944ae1e34.cert
theorem link_56e4849a55cd0392 : (parseCert L6.Certs.C56e4849a55cd0392).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C56e4849a55cd0392.certH.nvar, L6CheckK.F4.C56e4849a55cd0392.certH.fixed, L6CheckK.F4.C56e4849a55cd0392.certH.gens, L6CheckK.F4.C56e4849a55cd0392.certH.h) := by native_decide
theorem meaning_56e4849a55cd0392 : ∃ c, parseCert L6.Certs.C56e4849a55cd0392 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_56e4849a55cd0392 L6CheckK.F4.C56e4849a55cd0392.cert
theorem link_5701e0a62003d460 : (parseCert L6.Certs.C5701e0a62003d460).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5701e0a62003d460.certH.nvar, L6CheckK.F4.C5701e0a62003d460.certH.fixed, L6CheckK.F4.C5701e0a62003d460.certH.gens, L6CheckK.F4.C5701e0a62003d460.certH.h) := by native_decide
theorem meaning_5701e0a62003d460 : ∃ c, parseCert L6.Certs.C5701e0a62003d460 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5701e0a62003d460 L6CheckK.F4.C5701e0a62003d460.cert
theorem link_57184cd72518fed4 : (parseCert L6.Certs.C57184cd72518fed4).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C57184cd72518fed4.certH.nvar, L6CheckK.F4.C57184cd72518fed4.certH.fixed, L6CheckK.F4.C57184cd72518fed4.certH.gens, L6CheckK.F4.C57184cd72518fed4.certH.h) := by native_decide
theorem meaning_57184cd72518fed4 : ∃ c, parseCert L6.Certs.C57184cd72518fed4 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_57184cd72518fed4 L6CheckK.F4.C57184cd72518fed4.cert
theorem link_5734369cab42a80d : (parseCert L6.Certs.C5734369cab42a80d).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5734369cab42a80d.certH.nvar, L6CheckK.F4.C5734369cab42a80d.certH.fixed, L6CheckK.F4.C5734369cab42a80d.certH.gens, L6CheckK.F4.C5734369cab42a80d.certH.h) := by native_decide
theorem meaning_5734369cab42a80d : ∃ c, parseCert L6.Certs.C5734369cab42a80d = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5734369cab42a80d L6CheckK.F4.C5734369cab42a80d.cert
theorem link_5783079c59a1550b : (parseCert L6.Certs.C5783079c59a1550b).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5783079c59a1550b.certH.nvar, L6CheckK.F4.C5783079c59a1550b.certH.fixed, L6CheckK.F4.C5783079c59a1550b.certH.gens, L6CheckK.F4.C5783079c59a1550b.certH.h) := by native_decide
theorem meaning_5783079c59a1550b : ∃ c, parseCert L6.Certs.C5783079c59a1550b = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5783079c59a1550b L6CheckK.F4.C5783079c59a1550b.cert
theorem link_5783f922e65f69eb : (parseCert L6.Certs.C5783f922e65f69eb).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C5783f922e65f69eb.certH.nvar, L6CheckK.F4.C5783f922e65f69eb.certH.fixed, L6CheckK.F4.C5783f922e65f69eb.certH.gens, L6CheckK.F4.C5783f922e65f69eb.certH.h) := by native_decide
theorem meaning_5783f922e65f69eb : ∃ c, parseCert L6.Certs.C5783f922e65f69eb = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_5783f922e65f69eb L6CheckK.F4.C5783f922e65f69eb.cert
theorem link_57b00b6081bb0cf0 : (parseCert L6.Certs.C57b00b6081bb0cf0).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C57b00b6081bb0cf0.certH.nvar, L6CheckK.F4.C57b00b6081bb0cf0.certH.fixed, L6CheckK.F4.C57b00b6081bb0cf0.certH.gens, L6CheckK.F4.C57b00b6081bb0cf0.certH.h) := by native_decide
theorem meaning_57b00b6081bb0cf0 : ∃ c, parseCert L6.Certs.C57b00b6081bb0cf0 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_57b00b6081bb0cf0 L6CheckK.F4.C57b00b6081bb0cf0.cert
theorem link_57b1bef2cd072552 : (parseCert L6.Certs.C57b1bef2cd072552).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C57b1bef2cd072552.certH.nvar, L6CheckK.F4.C57b1bef2cd072552.certH.fixed, L6CheckK.F4.C57b1bef2cd072552.certH.gens, L6CheckK.F4.C57b1bef2cd072552.certH.h) := by native_decide
theorem meaning_57b1bef2cd072552 : ∃ c, parseCert L6.Certs.C57b1bef2cd072552 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_57b1bef2cd072552 L6CheckK.F4.C57b1bef2cd072552.cert
theorem link_57c2b2f3ce64f2cc : (parseCert L6.Certs.C57c2b2f3ce64f2cc).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.C57c2b2f3ce64f2cc.certH.nvar, L6CheckK.F4.C57c2b2f3ce64f2cc.certH.fixed, L6CheckK.F4.C57c2b2f3ce64f2cc.certH.gens, L6CheckK.F4.C57c2b2f3ce64f2cc.certH.h) := by native_decide
theorem meaning_57c2b2f3ce64f2cc : ∃ c, parseCert L6.Certs.C57c2b2f3ce64f2cc = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_57c2b2f3ce64f2cc L6CheckK.F4.C57c2b2f3ce64f2cc.cert

end L6CheckK.F4Link
