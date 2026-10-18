import L6Poly.Basic
import L6Check.Certs.C3470cf11f9e89256

/-! Cofactor certificates, batch 10: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_3470cf11f9e89256 : L6.Poly.checkCert L6.Certs.C3470cf11f9e89256 = true := by native_decide

end L6.Poly.Checks
