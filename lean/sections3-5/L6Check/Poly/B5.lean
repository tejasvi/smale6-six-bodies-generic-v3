import L6Poly.Basic
import L6Check.Certs.C242c0a990a09d8e6

/-! Cofactor certificates, batch 5: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_242c0a990a09d8e6 : L6.Poly.checkCert L6.Certs.C242c0a990a09d8e6 = true := by native_decide

end L6.Poly.Checks
