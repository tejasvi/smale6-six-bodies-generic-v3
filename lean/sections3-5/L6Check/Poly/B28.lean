import L6Poly.Basic
import L6Check.Certs.C957be199b7c614c7

/-! Cofactor certificates, batch 28: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_957be199b7c614c7 : L6.Poly.checkCert L6.Certs.C957be199b7c614c7 = true := by native_decide

end L6.Poly.Checks
