import L6Poly.Basic
import L6Check.Certs.Cd2101510a56ccb71

/-! Cofactor certificates, batch 40: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_d2101510a56ccb71 : L6.Poly.checkCert L6.Certs.Cd2101510a56ccb71 = true := by native_decide

end L6.Poly.Checks
