import L6Poly.Basic
import L6Check.Certs.C5a4228c851228eb8

/-! Cofactor certificates, batch 18: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_5a4228c851228eb8 : L6.Poly.checkCert L6.Certs.C5a4228c851228eb8 = true := by native_decide

end L6.Poly.Checks
