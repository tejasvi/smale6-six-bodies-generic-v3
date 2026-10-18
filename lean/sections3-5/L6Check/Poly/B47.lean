import L6Poly.Basic
import L6Check.Certs.Ce935bca79ddba857

/-! Cofactor certificates, batch 47: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_e935bca79ddba857 : L6.Poly.checkCert L6.Certs.Ce935bca79ddba857 = true := by native_decide

end L6.Poly.Checks
