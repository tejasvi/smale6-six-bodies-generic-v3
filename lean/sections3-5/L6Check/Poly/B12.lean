import L6Poly.Basic
import L6Check.Certs.C35572662f45b6cb5

/-! Cofactor certificates, batch 12: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_35572662f45b6cb5 : L6.Poly.checkCert L6.Certs.C35572662f45b6cb5 = true := by native_decide

end L6.Poly.Checks
