import L6Poly.Basic
import L6Check.Certs.Cbf1045e3e0922710

/-! Cofactor certificates, batch 33: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_bf1045e3e0922710 : L6.Poly.checkCert L6.Certs.Cbf1045e3e0922710 = true := by native_decide

end L6.Poly.Checks
