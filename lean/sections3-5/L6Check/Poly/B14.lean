import L6Poly.Basic
import L6Check.Certs.C42955a12632fff8e

/-! Cofactor certificates, batch 14: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_42955a12632fff8e : L6.Poly.checkCert L6.Certs.C42955a12632fff8e = true := by native_decide

end L6.Poly.Checks
