import L6Poly.Basic
import L6Check.Certs.C553c67900281f55f

/-! Cofactor certificates, batch 17: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_553c67900281f55f : L6.Poly.checkCert L6.Certs.C553c67900281f55f = true := by native_decide

end L6.Poly.Checks
