import L6Poly.Basic
import L6Check.Certs.Cbbfdf82e3e6adfc3

/-! Cofactor certificates, batch 32: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_bbfdf82e3e6adfc3 : L6.Poly.checkCert L6.Certs.Cbbfdf82e3e6adfc3 = true := by native_decide

end L6.Poly.Checks
