import L6Poly.Basic
import L6Check.Certs.Cc3eac6d02e27a678

/-! Cofactor certificates, batch 36: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_c3eac6d02e27a678 : L6.Poly.checkCert L6.Certs.Cc3eac6d02e27a678 = true := by native_decide

end L6.Poly.Checks
