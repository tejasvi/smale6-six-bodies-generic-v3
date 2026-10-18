import L6Poly.Basic
import L6Check.Certs.Cc9273cecc33f2aca

/-! Cofactor certificates, batch 38: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_c9273cecc33f2aca : L6.Poly.checkCert L6.Certs.Cc9273cecc33f2aca = true := by native_decide

end L6.Poly.Checks
