import L6Poly.Basic
import L6Check.Certs.C3ae64471a7598c39

/-! Cofactor certificates, batch 13: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_3ae64471a7598c39 : L6.Poly.checkCert L6.Certs.C3ae64471a7598c39 = true := by native_decide

end L6.Poly.Checks
