import L6Poly.Basic
import L6Check.Certs.Cffa2ee29f5ac013e

/-! Cofactor certificates, batch 55: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_ffa2ee29f5ac013e : L6.Poly.checkCert L6.Certs.Cffa2ee29f5ac013e = true := by native_decide

end L6.Poly.Checks
