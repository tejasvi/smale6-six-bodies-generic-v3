import L6Poly.Basic
import L6Check.Certs.Cf8c6533ac87c6478

/-! Cofactor certificates, batch 51: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_f8c6533ac87c6478 : L6.Poly.checkCert L6.Certs.Cf8c6533ac87c6478 = true := by native_decide

end L6.Poly.Checks
