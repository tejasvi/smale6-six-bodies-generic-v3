import L6Poly.Basic
import L6Check.Certs.C31a1929c3604b3e1

/-! Cofactor certificates, batch 7: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_31a1929c3604b3e1 : L6.Poly.checkCert L6.Certs.C31a1929c3604b3e1 = true := by native_decide

end L6.Poly.Checks
