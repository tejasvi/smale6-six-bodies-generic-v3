import L6Poly.Basic
import L6Check.Certs.C4aa4f52f05514ca4

/-! Cofactor certificates, batch 15: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_4aa4f52f05514ca4 : L6.Poly.checkCert L6.Certs.C4aa4f52f05514ca4 = true := by native_decide

end L6.Poly.Checks
