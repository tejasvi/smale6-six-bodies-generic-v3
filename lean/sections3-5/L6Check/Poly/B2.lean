import L6Poly.Basic
import L6Check.Certs.C1826e71d634e3773

/-! Cofactor certificates, batch 2: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_1826e71d634e3773 : L6.Poly.checkCert L6.Certs.C1826e71d634e3773 = true := by native_decide

end L6.Poly.Checks
