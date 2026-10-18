import L6Poly.Basic
import L6Check.Certs.Ca6ddcd4d8be768b9

/-! Cofactor certificates, batch 30: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_a6ddcd4d8be768b9 : L6.Poly.checkCert L6.Certs.Ca6ddcd4d8be768b9 = true := by native_decide

end L6.Poly.Checks
