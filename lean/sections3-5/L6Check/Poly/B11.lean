import L6Poly.Basic
import L6Check.Certs.C34adb611beeb99ee

/-! Cofactor certificates, batch 11: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_34adb611beeb99ee : L6.Poly.checkCert L6.Certs.C34adb611beeb99ee = true := by native_decide

end L6.Poly.Checks
