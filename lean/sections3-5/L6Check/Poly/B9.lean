import L6Poly.Basic
import L6Check.Certs.C33f8c2061ae65f1c

/-! Cofactor certificates, batch 9: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_33f8c2061ae65f1c : L6.Poly.checkCert L6.Certs.C33f8c2061ae65f1c = true := by native_decide

end L6.Poly.Checks
