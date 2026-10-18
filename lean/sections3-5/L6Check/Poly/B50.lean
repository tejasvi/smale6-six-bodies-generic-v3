import L6Poly.Basic
import L6Check.Certs.Cf1c0efc1e2010891

/-! Cofactor certificates, batch 50: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_f1c0efc1e2010891 : L6.Poly.checkCert L6.Certs.Cf1c0efc1e2010891 = true := by native_decide

end L6.Poly.Checks
