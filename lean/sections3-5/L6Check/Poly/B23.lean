import L6Poly.Basic
import L6Check.Certs.C81ff47566ee05742

/-! Cofactor certificates, batch 23: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_81ff47566ee05742 : L6.Poly.checkCert L6.Certs.C81ff47566ee05742 = true := by native_decide

end L6.Poly.Checks
