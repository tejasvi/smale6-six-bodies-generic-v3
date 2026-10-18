import L6Poly.Basic
import L6Check.Certs.C61f78e71f634f56d

/-! Cofactor certificates, batch 19: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_61f78e71f634f56d : L6.Poly.checkCert L6.Certs.C61f78e71f634f56d = true := by native_decide

end L6.Poly.Checks
