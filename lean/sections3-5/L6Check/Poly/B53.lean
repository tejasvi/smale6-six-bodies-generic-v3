import L6Poly.Basic
import L6Check.Certs.Cfc934afe0c2723c4

/-! Cofactor certificates, batch 53: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_fc934afe0c2723c4 : L6.Poly.checkCert L6.Certs.Cfc934afe0c2723c4 = true := by native_decide

end L6.Poly.Checks
