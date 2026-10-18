import L6SoundK.F4.Link
import L6Check.Certs.Cff43bc6544921b38
import L6Check.Certs.Cff4dcbb1db45f476
import L6Check.Certs.Cff64d58aa00f3f81
import L6Check.Certs.Cff8fac60dcde652d
import L6Check.Certs.Cffa2ee29f5ac013e
import L6Check.Certs.Cffb88cadf78c9cc6
import L6Check.Certs.Cffbf722c0be74172
import L6Check.Certs.Cffe2e7616b8257cf
import L6CheckK.F4.P174
import L6CheckK.F4.M30
import L6CheckK.F4.Cffa2ee29f5ac013e.Data

set_option maxHeartbeats 0
-- the decidability instance of the 4-tuple equality is larger than the default bound
set_option synthInstance.maxSize 1024

/-! Links of the certificate texts to the literal certificates, certificates 1920–1927. -/

namespace L6CheckK.F4Link

open L6.Poly

theorem link_ff43bc6544921b38 : (parseCert L6.Certs.Cff43bc6544921b38).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.Cff43bc6544921b38.certH.nvar, L6CheckK.F4.Cff43bc6544921b38.certH.fixed, L6CheckK.F4.Cff43bc6544921b38.certH.gens, L6CheckK.F4.Cff43bc6544921b38.certH.h) := by native_decide
theorem meaning_ff43bc6544921b38 : ∃ c, parseCert L6.Certs.Cff43bc6544921b38 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_ff43bc6544921b38 L6CheckK.F4.Cff43bc6544921b38.cert
theorem link_ff4dcbb1db45f476 : (parseCert L6.Certs.Cff4dcbb1db45f476).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.Cff4dcbb1db45f476.certH.nvar, L6CheckK.F4.Cff4dcbb1db45f476.certH.fixed, L6CheckK.F4.Cff4dcbb1db45f476.certH.gens, L6CheckK.F4.Cff4dcbb1db45f476.certH.h) := by native_decide
theorem meaning_ff4dcbb1db45f476 : ∃ c, parseCert L6.Certs.Cff4dcbb1db45f476 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_ff4dcbb1db45f476 L6CheckK.F4.Cff4dcbb1db45f476.cert
theorem link_ff64d58aa00f3f81 : (parseCert L6.Certs.Cff64d58aa00f3f81).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.Cff64d58aa00f3f81.certH.nvar, L6CheckK.F4.Cff64d58aa00f3f81.certH.fixed, L6CheckK.F4.Cff64d58aa00f3f81.certH.gens, L6CheckK.F4.Cff64d58aa00f3f81.certH.h) := by native_decide
theorem meaning_ff64d58aa00f3f81 : ∃ c, parseCert L6.Certs.Cff64d58aa00f3f81 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_ff64d58aa00f3f81 L6CheckK.F4.Cff64d58aa00f3f81.cert
theorem link_ff8fac60dcde652d : (parseCert L6.Certs.Cff8fac60dcde652d).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.Cff8fac60dcde652d.certH.nvar, L6CheckK.F4.Cff8fac60dcde652d.certH.fixed, L6CheckK.F4.Cff8fac60dcde652d.certH.gens, L6CheckK.F4.Cff8fac60dcde652d.certH.h) := by native_decide
theorem meaning_ff8fac60dcde652d : ∃ c, parseCert L6.Certs.Cff8fac60dcde652d = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_ff8fac60dcde652d L6CheckK.F4.Cff8fac60dcde652d.cert
theorem link_ffa2ee29f5ac013e : (parseCert L6.Certs.Cffa2ee29f5ac013e).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.Cffa2ee29f5ac013e.certH.nvar, L6CheckK.F4.Cffa2ee29f5ac013e.certH.fixed, L6CheckK.F4.Cffa2ee29f5ac013e.certH.gens, L6CheckK.F4.Cffa2ee29f5ac013e.certH.h) := by native_decide
theorem meaning_ffa2ee29f5ac013e : ∃ c, parseCert L6.Certs.Cffa2ee29f5ac013e = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_ffa2ee29f5ac013e L6CheckK.F4.Cffa2ee29f5ac013e.cert
theorem link_ffb88cadf78c9cc6 : (parseCert L6.Certs.Cffb88cadf78c9cc6).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.Cffb88cadf78c9cc6.certH.nvar, L6CheckK.F4.Cffb88cadf78c9cc6.certH.fixed, L6CheckK.F4.Cffb88cadf78c9cc6.certH.gens, L6CheckK.F4.Cffb88cadf78c9cc6.certH.h) := by native_decide
theorem meaning_ffb88cadf78c9cc6 : ∃ c, parseCert L6.Certs.Cffb88cadf78c9cc6 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_ffb88cadf78c9cc6 L6CheckK.F4.Cffb88cadf78c9cc6.cert
theorem link_ffbf722c0be74172 : (parseCert L6.Certs.Cffbf722c0be74172).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.Cffbf722c0be74172.certH.nvar, L6CheckK.F4.Cffbf722c0be74172.certH.fixed, L6CheckK.F4.Cffbf722c0be74172.certH.gens, L6CheckK.F4.Cffbf722c0be74172.certH.h) := by native_decide
theorem meaning_ffbf722c0be74172 : ∃ c, parseCert L6.Certs.Cffbf722c0be74172 = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_ffbf722c0be74172 L6CheckK.F4.Cffbf722c0be74172.cert
theorem link_ffe2e7616b8257cf : (parseCert L6.Certs.Cffe2e7616b8257cf).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (L6CheckK.F4.Cffe2e7616b8257cf.certH.nvar, L6CheckK.F4.Cffe2e7616b8257cf.certH.fixed, L6CheckK.F4.Cffe2e7616b8257cf.certH.gens, L6CheckK.F4.Cffe2e7616b8257cf.certH.h) := by native_decide
theorem meaning_ffe2e7616b8257cf : ∃ c, parseCert L6.Certs.Cffe2e7616b8257cf = some c ∧ CertMeaning c := L6K.F4.meaning_of_link link_ffe2e7616b8257cf L6CheckK.F4.Cffe2e7616b8257cf.cert

end L6CheckK.F4Link
