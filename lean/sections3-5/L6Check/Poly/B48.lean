import L6Poly.Basic
import L6Check.Certs.Cedaebdbfb40d7e27

/-! Cofactor certificates, batch 48: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_edaebdbfb40d7e27 : L6.Poly.checkCert L6.Certs.Cedaebdbfb40d7e27 = true := by native_decide

end L6.Poly.Checks
