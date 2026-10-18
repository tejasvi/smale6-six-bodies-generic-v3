import L6Poly.Basic
import L6Check.Certs.C87704ca9f9c75447

/-! Cofactor certificates, batch 24: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_87704ca9f9c75447 : L6.Poly.checkCert L6.Certs.C87704ca9f9c75447 = true := by native_decide

end L6.Poly.Checks
