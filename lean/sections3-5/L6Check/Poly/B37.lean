import L6Poly.Basic
import L6Check.Certs.Cc7138a4ede6fb116

/-! Cofactor certificates, batch 37: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_c7138a4ede6fb116 : L6.Poly.checkCert L6.Certs.Cc7138a4ede6fb116 = true := by native_decide

end L6.Poly.Checks
