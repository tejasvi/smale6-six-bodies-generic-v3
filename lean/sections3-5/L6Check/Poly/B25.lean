import L6Poly.Basic
import L6Check.Certs.C8b9a53daae8c51bb

/-! Cofactor certificates, batch 25: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_8b9a53daae8c51bb : L6.Poly.checkCert L6.Certs.C8b9a53daae8c51bb = true := by native_decide

end L6.Poly.Checks
