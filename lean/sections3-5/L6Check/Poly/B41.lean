import L6Poly.Basic
import L6Check.Certs.Cdabfd0fabd0b3f0c

/-! Cofactor certificates, batch 41: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_dabfd0fabd0b3f0c : L6.Poly.checkCert L6.Certs.Cdabfd0fabd0b3f0c = true := by native_decide

end L6.Poly.Checks
