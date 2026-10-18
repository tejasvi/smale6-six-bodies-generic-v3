import L6Poly.Basic
import L6Check.Certs.Cca083f86e77fc3e8

/-! Cofactor certificates, batch 39: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_ca083f86e77fc3e8 : L6.Poly.checkCert L6.Certs.Cca083f86e77fc3e8 = true := by native_decide

end L6.Poly.Checks
