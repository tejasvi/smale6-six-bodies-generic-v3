import L6Poly.Basic
import L6Check.Certs.Cdb739b621927d06a

/-! Cofactor certificates, batch 42: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_db739b621927d06a : L6.Poly.checkCert L6.Certs.Cdb739b621927d06a = true := by native_decide

end L6.Poly.Checks
