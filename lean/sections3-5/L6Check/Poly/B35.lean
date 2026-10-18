import L6Poly.Basic
import L6Check.Certs.Cc08dc59867d5c2c1

/-! Cofactor certificates, batch 35: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_c08dc59867d5c2c1 : L6.Poly.checkCert L6.Certs.Cc08dc59867d5c2c1 = true := by native_decide

end L6.Poly.Checks
