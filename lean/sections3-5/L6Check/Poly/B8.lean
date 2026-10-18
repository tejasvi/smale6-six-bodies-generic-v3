import L6Poly.Basic
import L6Check.Certs.C3394c79dff5a914d

/-! Cofactor certificates, batch 8: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_3394c79dff5a914d : L6.Poly.checkCert L6.Certs.C3394c79dff5a914d = true := by native_decide

end L6.Poly.Checks
