import L6Poly.Basic
import L6Check.Certs.Cf02fb0442bc90ef6

/-! Cofactor certificates, batch 49: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_f02fb0442bc90ef6 : L6.Poly.checkCert L6.Certs.Cf02fb0442bc90ef6 = true := by native_decide

end L6.Poly.Checks
