import L6Poly.Basic
import L6Check.Certs.C9052f6a64414d61a

/-! Cofactor certificates, batch 27: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_9052f6a64414d61a : L6.Poly.checkCert L6.Certs.C9052f6a64414d61a = true := by native_decide

end L6.Poly.Checks
