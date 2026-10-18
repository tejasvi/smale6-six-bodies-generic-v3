import L6Poly.Basic
import L6Check.Certs.Ce810814dbbbd618f

/-! Cofactor certificates, batch 46: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_e810814dbbbd618f : L6.Poly.checkCert L6.Certs.Ce810814dbbbd618f = true := by native_decide

end L6.Poly.Checks
