import L6Poly.Basic
import L6Check.Certs.C1459bbf4f7537687

/-! Cofactor certificates, batch 1: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_1459bbf4f7537687 : L6.Poly.checkCert L6.Certs.C1459bbf4f7537687 = true := by native_decide

end L6.Poly.Checks
